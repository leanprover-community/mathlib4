from typing import Dict, Optional, Union, Tuple, List
import yaml
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
  with open(fn, 'w') as out:
    for (id, val) in pairs:
      out.write(f'{id}\n{val.strip()}\n\n')

hundred_yaml = sys.argv[1]
overview_yaml = sys.argv[2]
undergrad_yaml = sys.argv[3]

with open(hundred_yaml, 'r') as hy:
  hundred = yaml.safe_load(hy)
with open(overview_yaml, 'r') as hy:
  overview = yaml.safe_load(hy)
with open(undergrad_yaml, 'r') as hy:
  undergrad = yaml.safe_load(hy)

hundred_decls:List[Tuple[str, str]] = []

for index, entry in hundred.items():
  if 'decl' in entry:
    hundred_decls.append((index, entry['decl']))
  elif 'decls' in entry:
    hundred_decls = hundred_decls + [(index, d) for d in entry['decls']]

overview_decls = tiered_extract(overview)
assert all(len(n) == 3 for n, _ in overview_decls)
overview_decls = flatten_names(overview_decls)

undergrad_decls = tiered_extract(undergrad)
assert all(len(n) >= 3 for n, _ in undergrad_decls)
undergrad_decls = flatten_names(undergrad_decls)

print_list('100.txt', hundred_decls)
print_list('overview.txt', overview_decls)
print_list('undergrad.txt', undergrad_decls)
