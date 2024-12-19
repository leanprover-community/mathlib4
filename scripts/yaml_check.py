"""
This file reads in the four yaml files, and translates them to simpler json files
that are easier to process in Lean.

Usage:
  python3 yaml_check.py <100.yaml> <1000.yaml> <overview.yaml> <undergrad.yaml>

(Each <name> is the path to a yaml file containing information about the respective class
 of theorems. The order of these files is important.)

"""
from typing import Dict, Mapping, Optional, Union, Tuple, List
from dataclasses import dataclass
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

# keep in sync with make_site.py in the leanprover-community.github.io repo
@dataclass
class DocDecl:
    name: str
    decl_header_html: str
    docs_link: str
    src_link: str

# keep in sync with make_site.py in the leanprover-community.github.io repo
@dataclass
class HundredTheorem:
    number: str
    title: str
    decl: Optional[str] = None
    decls: Optional[List[str]] = None
    doc_decls: Optional[List[DocDecl]] = None
    author: Optional[str] = None
    links: Optional[Mapping[str, str]] = None
    note: Optional[str] = None

# keep in sync with make_site.py in the leanprover-community.github.io repo
@dataclass
class ThousandPlusTheorem:
    # Wikidata identifier (the letter Q followed by a string as digits),
    # optionally followed by a letter (such as "A", "B" or "X" for disambiguation).
    # "Q1008566" and "Q4724004A" are valid identifiers, for example.
    wikidata: str
    title: str
    decl: Optional[str] = None
    decls: Optional[List[str]] = None
    doc_decls: Optional[List[DocDecl]] = None
    author: Optional[str] = None
    date: Optional[str] = None
    url: Optional[str] = None
    note: Optional[str] = None
    url: Optional[str] = None

hundred_yaml = sys.argv[1]
thousand_yaml = sys.argv[2]
overview_yaml = sys.argv[3]
undergrad_yaml = sys.argv[4]

with open(hundred_yaml, 'r', encoding='utf8') as hy:
  hundred = yaml.safe_load(hy)
with open(thousand_yaml, 'r', encoding='utf8') as hy:
  thousand = yaml.safe_load(hy)
with open(overview_yaml, 'r', encoding='utf8') as hy:
  overview = yaml.safe_load(hy)
with open(undergrad_yaml, 'r', encoding='utf8') as hy:
  undergrad = yaml.safe_load(hy)

hundred_decls: List[Tuple[str, str]] = []

for index, entry in hundred.items():
  # check that the YAML fits the dataclass used in the website
  _thm = HundredTheorem(index, **entry)
  title = entry['title']
  if 'decl' in entry:
    hundred_decls.append((f'{index} {title}', entry['decl']))
  elif 'decls' in entry:
    if not isinstance(entry['decls'], list):
      raise ValueError(f"For key {index} ({title}): did you mean `decl` instead of `decls`?")
    hundred_decls = hundred_decls + [(f'{index} {title}', d) for d in entry['decls']]

thousand_decls: List[Tuple[str, str]] = []
for index, entry in thousand.items():
  # check that the YAML fits the dataclass used in the website
  _thm = ThousandPlusTheorem(index, **entry)
  title = entry['title']
  if 'decl' in entry:
    thousand_decls.append((f'{index} {title}', entry['decl']))
  elif 'decls' in entry:
    if not isinstance(entry['decls'], list):
      raise ValueError(f"For key {index} ({title}): did you mean `decl` instead of `decls`?")
    thousand_decls = thousand_decls + [(f'{index} {title}', d) for d in entry['decls']]

overview_decls = tiered_extract(overview)
assert all(len(n) == 3 for n, _ in overview_decls)
overview_decls = flatten_names(overview_decls)

undergrad_decls = tiered_extract(undergrad)
assert all(len(n) >= 3 for n, _ in undergrad_decls)
undergrad_decls = flatten_names(undergrad_decls)

with open('100.json', 'w', encoding='utf8') as f:
  json.dump(hundred_decls, f)
with open('1000.json', 'w', encoding='utf8') as f:
  json.dump(thousand_decls, f)
with open('overview.json', 'w', encoding='utf8') as f:
  json.dump(overview_decls, f)
with open('undergrad.json', 'w', encoding='utf8') as f:
  json.dump(undergrad_decls, f)
