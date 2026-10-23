"""Compatibility import for historical scripts; use the independent public oracle.

This file intentionally defines no orchestration or proof-checking behavior.
The isolated reproduction layout places check_semantics.py beside this file.
"""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE if (HERE/'check_semantics.py').exists() else HERE.parent))
from check_semantics import absolute
