#!/usr/bin/env python3
"""Rebuild HTML reading editions; optionally rewrite checksums after deliberate edits."""
from pathlib import Path
import argparse
from spec_support import render_all, write_checksums

def main() -> None:
    ap=argparse.ArgumentParser();ap.add_argument('directory',nargs='?',default=str(Path(__file__).resolve().parent));ap.add_argument('--checksums',action='store_true')
    args=ap.parse_args();root=Path(args.directory).resolve();render_all(root)
    if args.checksums:write_checksums(root)
    print('Rendered three reading editions. No language conformance tests executed.')
if __name__=='__main__':main()
