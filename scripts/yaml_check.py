"""
This file is copied from the mathlib3 file of the same name.
It reads in the three yaml files, and translates them to simpler json files that are easier to
process in Lean.
"""
from typing import Dict, Optional, Union, Tuple, List
import yaml
import json
import sys

TieredDict = Dict[str, Union[Optional[str], 'TieredDict']]

def tiered_extract(db: TieredDict) -> List[Tuple[List[str], str]]:
  """From a nested dictionary, return a list of (key_path, values)
  of the deepest level."""
  out = []
  for name, entry in db.items():
    if isinstance(entry, dict):
      for subname, value in tiered_extract(entry):
        out.append(([name] + subname, value))
    else:
      if entry and '/' not in entry:
        out.append(([name], entry))
  return out

def flatten_names(data: List[Tuple[List[str], str]]) -> List[Tuple[str, str]]:
  return [(' :: '.join(id), v) for id, v in data]

def print_list(fn: str, pairs: List[Tuple[str, str]]) -> None:
  with open(fn, 'w', encoding='utf8') as out:
    for (id, val) in pairs:
      out.write(f'{id}\n{val.strip()}\n\n')

hundred_yaml = sys.argv[1]
overview_yaml = sys.argv[2]
undergrad_yaml = sys.argv[3]

with open(hundred_yaml, 'r', encoding='utf8') as hy:
  hundred = yaml.safe_load(hy)
with open(overview_yaml, 'r', encoding='utf8') as hy:
  overview = yaml.safe_load(hy)
with open(undergrad_yaml, 'r', encoding='utf8') as hy:
  undergrad = yaml.safe_load(hy)

hundred_decls:List[Tuple[str, str]] = []

for index, entry in hundred.items():
  title = entry['title']
  if 'decl' in entry:
    hundred_decls.append((f'{index} {title}', entry['decl']))
  elif 'decls' in entry:
    if not isinstance(entry['decls'], list):
      raise ValueError(f"For key {index} ({title}): did you mean `decl` instead of `decls`?")
    hundred_decls = hundred_decls + [(f'{index} {title}', d) for d in entry['decls']]

overview_decls = tiered_extract(overview)
assert all(len(n) == 3 for n, _ in overview_decls)
overview_decls = flatten_names(overview_decls)

undergrad_decls = tiered_extract(undergrad)
assert all(len(n) >= 3 for n, _ in undergrad_decls)
undergrad_decls = flatten_names(undergrad_decls)

with open('100.json', 'w', encoding='utf8') as f:
  json.dump(hundred_decls, f)
with open('overview.json', 'w', encoding='utf8') as f:
  json.dump(overview_decls, f)
with open('undergrad.json', 'w', encoding='utf8') as f:
  json.dump(undergrad_decls, f)
