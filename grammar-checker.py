#!/usr/bin/env python3
import os
import sys
import parglare

if __name__ == "__main__":
    if(len(sys.argv) < 2):
        print("A file argument is required")
        exit(1)
    grammar = parglare.Grammar.from_file(sys.argv[1])
    print(grammar.productions)