#!/usr/bin/env python3
"""Submit one prompt to a fresh ChatGPT Brave tab with a hard active-tab cap."""

import argparse
import base64
import json
import subprocess
from pathlib import Path


def osa(script: str, *args: str) -> str:
    return subprocess.run(
        ["osascript", "-", *args], input=script, text=True,
        capture_output=True, check=True,
    ).stdout.strip()


COUNT = '''tell application "Brave Browser"
set best to 0
repeat with w in windows
 set n to 0
 repeat with t in tabs of w
  if URL of t starts with "https://chatgpt.com/c/" then set n to n + 1
 end repeat
 if n > best then set best to n
end repeat
return best as text
end tell'''


SUBMIT = '''on run argv
set payload to item 1 of argv
tell application "Brave Browser"
 if (count of windows) is 0 then make new window
 set w to front window
 set best to -1
 repeat with candidate in windows
  set n to 0
  repeat with oldTab in tabs of candidate
   if URL of oldTab starts with "https://chatgpt.com/c/" then set n to n + 1
  end repeat
  if n > best then
   set best to n
   set w to candidate
  end if
 end repeat
 set t to make new tab at end of tabs of w with properties {URL:"https://chatgpt.com/"}
 set active tab index of w to count of tabs of w
 set index of w to 1
 activate
 repeat 20 times
  delay 1
  try
   set ready to execute t javascript "!!document.querySelector('#prompt-textarea')"
   if ready then exit repeat
  end try
 end repeat
 set fillResult to execute t javascript "(() => {const e=document.querySelector('#prompt-textarea');if(!e)return 'NO_INPUT';const b='" & payload & "';const a=Uint8Array.from(atob(b),c=>c.charCodeAt(0));const s=new TextDecoder().decode(a);e.focus();document.execCommand('selectAll',false,null);document.execCommand('insertText',false,s);e.dispatchEvent(new InputEvent('input',{bubbles:true,inputType:'insertText',data:s}));return (e.innerText||e.textContent||'').length.toString()})()"
 delay 1
 set sendResult to execute t javascript "(() => {const b=document.querySelector('button[data-testid=send-button]');if(!b||b.disabled)return 'NO_SEND';b.click();return 'SENT'})()"
 delay 1
 return fillResult & "|" & sendResult & "|" & (URL of t)
end tell
end run'''


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("prompt", type=Path)
    p.add_argument("--cap", type=int, default=5)
    args = p.parse_args()
    active = int(osa(COUNT) or "0")
    if active >= args.cap:
        raise SystemExit(f"active generation cap reached: {active}/{args.cap}")
    text = args.prompt.read_text(encoding="utf-8")
    payload = base64.b64encode(text.encode()).decode()
    result = osa(SUBMIT, payload)
    print(json.dumps({"prompt": str(args.prompt), "active_before": active,
                      "result": result}))


if __name__ == "__main__":
    main()
