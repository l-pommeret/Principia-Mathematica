/-! PM I ✱94, first macro-lot, Gutenberg 78050 pp. 620–624. -/
namespace PM.Architecture.Star94Source
def canonicalSource := "https://www.gutenberg.org/files/78050/78050-src/78050-src.htm#Page_620"
def propositionIds := ["94.12","94.13","94.14","94.2","94.201","94.21","94.22",
  "94.3","94.31","94.401","94.41","94.42","94.43","94.441","94.442",
  "94.5","94.51","94.52","94.6","94.61","94.62","94.63","94.64"]
def verbatimStatements := [
  "⊢:P∈Potʻ(R|S).⊃.(∃T).T∈Potʻ(S|R).P|R=R|T",
  "⊢:T∈Potʻ(S|R).⊃.(∃P).P∈Potʻ(R|S).P|R=R|T",
  "⊢.|RʻʻPotʻ(R|S)=R|ʻʻPotʻ(S|R)",
  "⊢:P∈Potʻ(R|S)∪ιʻI.⊃.S|P|R∈Potʻ(S|R)",
  "⊢:T∈Potʻ(S|R).⊃.(∃P).P∈Potʻ(R|S)∪ιʻI.T=S|P|R",
  "⊢.Potʻ(S|R)=(S∥R)ʻʻ{Potʻ(R|S)∪ιʻI}",
  "⊢:ᗡʻR⊂DʻS.∨.DʻS⊂ᗡʻR:⊃.Potʻ(S|R)=S|ʻʻPotʻ(R|S)∪ιʻI",
  "⊢:R∈1→Cls.ᗡʻ(R|S)⊂DʻR.⊃:P∈Potʻ(R|S).⊃.(∃T).T∈Potʻ(S|R).P=R|T|R̆",
  "⊢:R∈1→Cls.ᗡʻ(R|S)⊂DʻR.⊃.Potʻ(R|S)=(R∥R̆)ʻʻPotʻ(S|R)",
  "⊢.pʻᗡʻʻPotʻ(R|S)=pʻᗡʻʻR|ʻʻS|ʻʻPotʻ(R|S)",
  "⊢:S∈1→Cls.ᗡʻ(S|R)⊂DʻS.⊃.pʻᗡʻʻPotʻ(R|S)=pʻDʻʻ|SʻʻPotʻ(S|R)",
  "⊢:R∈1→Cls.⊃.R̆ʻʻpʻᗡʻʻPotʻ(R|S)=pʻᗡʻʻ|RʻʻPotʻ(R|S)",
  "⊢:R,S∈1→Cls.ᗡʻ(S|R)⊂DʻS.⊃.R̆ʻʻpʻᗡʻʻPotʻ(R|S)=pʻᗡʻʻPotʻ(S|R)",
  "⊢:S∈1→Cls.ᗡʻ(S|R)⊂DʻS.⊃.pʻᗡʻʻPotʻ(R|S)=pʻᗡʻʻR|ʻʻPotʻ(S|R)",
  "⊢:R∈1→Cls.⊃.R̆ʻʻpʻᗡʻʻPotʻ(R|S)=pʻᗡʻʻR|ʻʻPotʻ(S|R)",
  "⊢.pʻᗡʻʻPotʻ(S|R)=pʻᗡʻʻR|ʻʻPotʻ(S|R)",
  "⊢:R∈1→Cls.⊃.pʻᗡʻʻPotʻ(S|R)=R̆ʻʻpʻᗡʻʻPotʻ(R|S)",
  "⊢:S∈1→Cls.ᗡʻ(S|R)⊂DʻS.⊃.pʻᗡʻʻPotʻ(R|S) sm pʻᗡʻʻPotʻ(S|R)",
  "⊢:R|S=S|R.⊃:M∈PotʻR.N∈PotʻS.⊃.M|N=N|M",
  "⊢:R|S=S|R.⊃:M∈PotʻR.⊃.M|Spo=Spo|M:N∈PotʻS.⊃.N|Rpo=Rpo|N",
  "⊢:R|S=S|R.⊃.Rpo|Spo=Spo|Rpo",
  "⊢:R|S=S|R.⊃.(R|S)po ⊂ Rpo|Spo",
  "⊢:R|S=S|R.⊃.(R|S)* ⊂ R*|S*"]
end PM.Architecture.Star94Source
