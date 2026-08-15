#!/usr/bin/env python3
"""Import completed ChatGPT answers from known Brave conversation tabs."""

import argparse
import base64
import json
import subprocess
from pathlib import Path


JS = r'''(() => {
 const u=[...document.querySelectorAll('[data-message-author-role="user"]')];
 const a=[...document.querySelectorAll('[data-message-author-role="assistant"]')];
 const z=a.at(-1), body=z&&(z.querySelector('.markdown,.prose')||z);
 const stop=!!document.querySelector('button[data-testid="stop-button"]');
 if(!body) return JSON.stringify({error:'no answer',stop});
 const c=body.cloneNode(true);
 [...c.querySelectorAll('[data-math-source]')].forEach(n=>{
   const tex=n.getAttribute('data-math-source')||'';
   const display=(n.style.display==='block'||n.querySelector('.katex-display'));
   n.replaceWith(document.createTextNode(display?'\n$$\n'+tex+'\n$$\n':'$'+tex+'$'));
 });
 const text=(c.innerText||c.textContent||'').trim();
 const enc=s=>{const v=new TextEncoder().encode(s);let x='';for(let i=0;i<v.length;i+=8192)x+=String.fromCharCode(...v.subarray(i,i+8192));return btoa(x)};
 return JSON.stringify({stop,count:a.length,prompt:enc(u.at(-1)?.innerText||''),answer:enc(text)});
})()'''


def extract(url: str, activate: bool = False) -> dict:
    script = '''on run argv
set targetURL to item 1 of argv
set probeJS to item 2 of argv
set shouldActivate to item 3 of argv
tell application "Brave Browser"
 repeat with wi from 1 to count of windows
  set w to window wi
  repeat with ti from 1 to count of tabs of w
   set t to tab ti of w
   if URL of t is targetURL then
    if shouldActivate is "1" then
     set active tab index of w to ti
     set index of w to 1
     activate
     delay 3
    end if
    return execute t javascript probeJS
   end if
  end repeat
 end repeat
end tell
return "NOT_FOUND"
end run'''
    result = subprocess.run(
        ["osascript", "-", url, JS, "1" if activate else "0"], input=script, text=True,
        capture_output=True, check=True,
    ).stdout.strip()
    if result == "NOT_FOUND":
        raise RuntimeError(f"Brave tab not found: {url}")
    return json.loads(result)


def decode(value: str) -> str:
    return base64.b64decode(value).decode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("url")
    parser.add_argument("output", type=Path)
    parser.add_argument("--activate", action="store_true",
                        help="wake a discarded Brave tab before extraction")
    args = parser.parse_args()
    data = extract(args.url, activate=args.activate)
    if "answer" not in data:
        raise SystemExit(data.get("error", "answer DOM is not loaded yet"))
    if data.get("stop"):
        raise SystemExit("response is still generating")
    answer = decode(data["answer"])
    if len(answer) < 200:
        raise SystemExit("response is unexpectedly short")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(answer + "\n", encoding="utf-8")
    print(json.dumps({"output": str(args.output), "chars": len(answer), "turns": data["count"]}))


if __name__ == "__main__":
    main()
