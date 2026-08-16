import copy
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import verify_dependencies as dependencies


class DependencyAuditTests(unittest.TestCase):
    def test_dependency_index_matches_short_exact_and_unique_suffix_names(self):
        aliases = {"lean_realizations": {}}
        declarations = {
            "PM.Left.alpha": "PM1:ONE",
            "PM.Right.beta": "PM1:TWO",
        }
        index = dependencies.DependencyIndex.build(declarations, aliases)
        self.assertEqual(index.by_short["alpha"], {"PM.Left.alpha"})
        self.assertEqual(index.by_suffix["Left.alpha"], {"PM.Left.alpha"})

    def test_qualified_identifier_scan_does_not_match_a_proper_prefix(self):
        matches = [match.group(1) for match in dependencies.LEAN_IDENTIFIER.finditer(
            "theorem t : True := Foo.bar.baz"
        )]
        self.assertIn("Foo.bar.baz", matches)
        self.assertNotIn("Foo.bar", matches)

    def test_dependency_index_preserves_derive_and_field_label_guards(self):
        aliases = {"lean_realizations": {}}
        declarations = {
            "PM.Derivation.derive": "PM1:ONE",
            "PM.Record.product": "PM1:TWO",
        }
        index = dependencies.DependencyIndex.build(declarations, aliases)
        body = "by exact { product := value, proof := derive h }"
        tokens = [token for token, _qualified in dependencies.lean_identifier_tokens(body)]
        self.assertNotIn("product", tokens)
        self.assertIn("derive", tokens)
        self.assertTrue(declarations["PM.Derivation.derive"])
        self.assertNotIn("PM.Derivation.derive", {
            name for token in tokens
            for name in index.by_short.get(token, ())
            if not name.endswith(".derive")
        })

    def test_pm_decimal_order_is_not_filename_order(self):
        self.assertLess(dependencies.pm_order("PM1:✱2·08"), dependencies.pm_order("PM1:✱2·1"))
        self.assertLess(dependencies.pm_order("PM1:✱2·1"), dependencies.pm_order("PM1:✱2·11"))
        self.assertLess(dependencies.pm_order("PM1:✱2·11"), dependencies.pm_order("PM1:✱2·33"))

    def test_current_kernel_checked_corpus_is_covered(self):
        graph = dependencies.audit(ROOT)
        checked = graph["coverage"]["audited_items"]
        expected_checked = sum(
            node["formal_status"] in ("kernel-checked", "awaiting-ci")
            for node in graph["nodes"]
        )
        self.assertEqual(checked, expected_checked)
        # The derived-facts migration deliberately reduced the presently
        # kernel-checked frontier; coverage must follow metadata, not preserve
        # a stale pre-migration cardinality.
        self.assertGreater(checked, 0)
        # The current frontier consists only of primitive constructors.  They
        # correctly have no dependency edges: requiring a nonempty graph here
        # encoded the superseded derived-facts/T12 architecture.
        self.assertEqual(graph["historical_graph"]["edges"], [])
        self.assertEqual(graph["lean_graph"]["edges"], [
            {"from": "PM1:✱1·4", "to": "PM.Derivation.star_1_4"},
            {"from": "PM1:✱1·5", "to": "PM.Derivation.star_1_5"},
            {"from": "PM1:✱1·6", "to": "PM.Derivation.star_1_6"},
        ])

    def test_detach_resolves_to_printed_function_rule(self):
        items = {item["id"]: item for item in dependencies.load_items(ROOT)}
        item = items["PM1:✱2·06"]
        # Removing Architecture legitimately left catalogued items undeclared.
        declarations = {
            candidate["declaration"]: candidate["id"]
            for candidate in items.values() if candidate.get("declaration")
        }
        actual = dependencies.extract_lean_dependencies(item, declarations, ROOT)
        normalized = dependencies.normalize(item, actual, declarations, ROOT)
        self.assertIn("PM1:✱1·11", normalized)
        self.assertNotIn("PM1:✱1·1", normalized)

    def test_unjustified_definition_bridge_is_rejected(self):
        items = {item["id"]: item for item in dependencies.load_items(ROOT)}
        item = copy.deepcopy(items["PM1:✱2·01"])
        item["dependency_justifications"][0]["evidence"] = ""
        # Removing Architecture legitimately left catalogued items undeclared.
        declarations = {
            candidate["declaration"]: candidate["id"]
            for candidate in items.values() if candidate.get("declaration")
        }
        actual = dependencies.extract_lean_dependencies(item, declarations, ROOT)
        with self.assertRaises(dependencies.DependencyError):
            dependencies.normalize(item, actual, declarations, ROOT)

    def test_unindexed_qualified_reference_is_rejected(self):
        item = {"id": "PM1:TEST"}
        with self.assertRaises(dependencies.DependencyError):
            dependencies.reject_unindexed_references(
                item, "theorem test : True := Classical.choice h", set()
            )

    def test_relaxed_dependency_alignment_requires_exact_differences_and_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "reviews").mkdir()
            (root / "reviews/attempt.json").write_text("{}", encoding="utf-8")
            item = {
                "id": "PM1:✱2·73",
                "printed_dependencies": ["PM1:✱2·38", "PM1:✱2·621"],
                "historical_dependency_relaxation": {
                    "classification": "relaxed-closure",
                    "added_beyond_print": ["PM1:✱1·6"],
                    "printed_but_unused": [],
                    "strict_attempt_evidence": "reviews/attempt.json",
                    "editorial_note": "A constrained attempt required Syll.",
                },
            }
            dependencies.verify_dependency_alignment(
                item, ["PM1:✱1·6", "PM1:✱2·38", "PM1:✱2·621"], root
            )
            bad = copy.deepcopy(item)
            bad["historical_dependency_relaxation"]["added_beyond_print"] = []
            with self.assertRaises(dependencies.DependencyError):
                dependencies.verify_dependency_alignment(
                    bad, ["PM1:✱1·6", "PM1:✱2·38", "PM1:✱2·621"], root
                )

    def test_nonlogical_assumption_registry_is_separate_and_known(self):
        graph = dependencies.audit(ROOT)
        ledger = graph["nonlogical_assumptions"]
        self.assertEqual(
            {record["id"] for record in ledger["registry"]},
            {"PM1:REDUCIBILITY", "PM2:INFINITY", "PM2:MULTIPLICATIVE"},
        )
        self.assertEqual(
            ledger["direct_edges"],
            # The maintainer's reducibility audit validated these 27 direct
            # uses of star_12_1/star_12_11, replacing the former five-edge list.
            [
                {"from": "PM1:✱12·1", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱12·11", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱20·13", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱21·112", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱21·12", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱21·13", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱22·33", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱22·34", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱22·35", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱23·33", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱23·34", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱23·35", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱33·101", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱33·102", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱33·103", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱33·1", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱34·1", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱35·1", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱35·101", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱35·102", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱35·103", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱40·1", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱40·11", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱41·1", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱41·11", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱50·1", "to": "PM1:REDUCIBILITY"},
                {"from": "PM1:✱52·1", "to": "PM1:REDUCIBILITY"},
            ],
        )
        # The same audited decision records the exact ten downstream inherited
        # dependencies instead of the former empty expectation.
        self.assertEqual(ledger["inherited_edges"], [
            {"from": "PM1:✱13·101", "to": "PM1:REDUCIBILITY"},
            {"from": "PM1:✱20·15", "to": "PM1:REDUCIBILITY"},
            {"from": "PM1:✱21·7", "to": "PM1:REDUCIBILITY"},
            {"from": "PM1:✱21·701", "to": "PM1:REDUCIBILITY"},
            {"from": "PM1:✱21·702", "to": "PM1:REDUCIBILITY"},
            {"from": "PM1:✱21·703", "to": "PM1:REDUCIBILITY"},
            {"from": "PM1:✱21·704", "to": "PM1:REDUCIBILITY"},
            {"from": "PM1:✱21·705", "to": "PM1:REDUCIBILITY"},
            {"from": "PM1:✱21·18", "to": "PM1:REDUCIBILITY"},
            {"from": "PM1:✱34·5", "to": "PM1:REDUCIBILITY"},
        ])
        self.assertNotIn("PM1:REDUCIBILITY", {node["id"] for node in graph["nodes"]})

    def test_assumption_closure_distinguishes_direct_and_inherited(self):
        registry = {"PM1:REDUCIBILITY": {"id": "PM1:REDUCIBILITY"}}
        items = [
            {"id": "PM1:✱12·1", "normalized_dependencies": [],
             "direct_assumptions": ["PM1:REDUCIBILITY"], "inherited_assumptions": []},
            {"id": "PM1:✱13·1", "normalized_dependencies": ["PM1:✱12·1"],
             "direct_assumptions": [], "inherited_assumptions": ["PM1:REDUCIBILITY"]},
        ]
        closure = dependencies.assumption_closure(items, registry)
        self.assertEqual(closure["PM1:✱12·1"]["direct"], ["PM1:REDUCIBILITY"])
        self.assertEqual(closure["PM1:✱13·1"]["inherited"], ["PM1:REDUCIBILITY"])

    def test_assumption_closure_requires_downstream_declaration(self):
        registry = {"PM1:REDUCIBILITY": {"id": "PM1:REDUCIBILITY"}}
        with self.assertRaises(dependencies.DependencyError):
            dependencies.assumption_closure([
                {"id": "PM1:✱12·1", "normalized_dependencies": [],
                 "direct_assumptions": ["PM1:REDUCIBILITY"], "inherited_assumptions": []},
                {"id": "PM1:✱13·1", "normalized_dependencies": ["PM1:✱12·1"]},
            ], registry)

    def test_assumption_closure_rejects_unknown_and_false_inheritance(self):
        registry = {"PM1:REDUCIBILITY": {"id": "PM1:REDUCIBILITY"}}
        with self.assertRaises(dependencies.DependencyError):
            dependencies.assumption_closure([
                {"id": "PM1:✱12·1", "normalized_dependencies": [],
                 "direct_assumptions": ["PM1:UNKNOWN"], "inherited_assumptions": []}
            ], registry)

    def test_explicit_assumption_parameter_is_verified(self):
        assumption = "PM1:REDUCIBILITY"
        lean_type = "PM.Experimental.PredicativeGateToy.UnaryReducibility12_1"
        item = {
            "id": "PM1:✱13·101",
            "assumption_parameters": {
                assumption: {"parameter": "reducibility", "lean_type": lean_type}
            },
        }
        usage = {"direct": [], "inherited": [assumption], "effective": [assumption]}
        registry = {assumption: {"lean_parameter_types": [lean_type]}}
        body = f"""theorem star_13_101
            (reducibility : {lean_type} signature function)
            (x y : Term) : Target := by
          exact use reducibility
        """
        evidence = dependencies.verify_assumption_parameters(item, usage, registry, body)
        self.assertEqual(evidence[0]["parameter"], "reducibility")

    def test_body_only_assumption_type_is_rejected(self):
        assumption = "PM1:REDUCIBILITY"
        lean_type = "PM.Experimental.PredicativeGateToy.UnaryReducibility12_1"
        item = {
            "id": "PM1:✱13·101",
            "assumption_parameters": {
                assumption: {"parameter": "reducibility", "lean_type": lean_type}
            },
        }
        usage = {"direct": [assumption], "inherited": [], "effective": [assumption]}
        registry = {assumption: {"lean_parameter_types": [lean_type]}}
        body = f"""theorem star_13_101 (h : Input) : Target := by
          let reducibility : {lean_type} signature function := hidden h
          exact use reducibility
        """
        with self.assertRaises(dependencies.DependencyError):
            dependencies.verify_assumption_parameters(item, usage, registry, body)

    def test_instance_assumption_parameter_is_rejected(self):
        assumption = "PM1:REDUCIBILITY"
        lean_type = "PM.Experimental.PredicativeGateToy.UnaryReducibility12_1"
        item = {
            "id": "PM1:✱13·101",
            "assumption_parameters": {
                assumption: {"parameter": "reducibility", "lean_type": lean_type}
            },
        }
        usage = {"direct": [assumption], "inherited": [], "effective": [assumption]}
        registry = {assumption: {"lean_parameter_types": [lean_type]}}
        body = (
            f"theorem star_13_101 "
            f"[reducibility : {lean_type} signature function] : Target := by exact proof"
        )
        with self.assertRaises(dependencies.DependencyError):
            dependencies.verify_assumption_parameters(item, usage, registry, body)

    def test_effective_assumption_requires_exact_binding_set_and_registered_type(self):
        assumption = "PM1:REDUCIBILITY"
        lean_type = "PM.Experimental.PredicativeGateToy.UnaryReducibility12_1"
        usage = {"direct": [assumption], "inherited": [], "effective": [assumption]}
        registry = {assumption: {"lean_parameter_types": [lean_type]}}
        with self.assertRaises(dependencies.DependencyError):
            dependencies.verify_assumption_parameters(
                {"id": "PM1:✱12·1"}, usage, registry,
                "theorem star_12_1 : Target := proof",
            )
        with self.assertRaises(dependencies.DependencyError):
            dependencies.verify_assumption_parameters(
                {
                    "id": "PM1:✱12·1",
                    "assumption_parameters": {
                        assumption: {"parameter": "r", "lean_type": "PM.Wrong.Type"}
                    },
                },
                usage,
                registry,
                "theorem star_12_1 (r : PM.Wrong.Type) : Target := proof",
            )
        with self.assertRaises(dependencies.DependencyError):
            dependencies.assumption_closure([
                {"id": "PM1:✱12·1", "normalized_dependencies": [],
                 "direct_assumptions": [], "inherited_assumptions": ["PM1:REDUCIBILITY"]}
            ], registry)


if __name__ == "__main__":
    unittest.main()
