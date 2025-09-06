from collections import Counter
from itertools import combinations
import matplotlib.pyplot as plt
import numpy as np

NUMBER_NAMESPACES = 80

# Read in all the names from constants.txt
with open('constants.txt', 'r') as f:
    constants = f.read().splitlines()

constants = [(".".join(c.split('.')[:-1]), c.split('.')[-1]) for c in constants]

constants = sorted(constants, key=lambda x: len(x[0]))

# remove with empty namespaces
constants = [c for c in constants if c[0]]

# get the unique namespaces with the number of occurrences
# namespaces = set([c[0] for c in constants])
namespaces_counter = Counter()
for c in constants:
    namespaces_counter[c[0]] += 1

constants = set(constants)

values = set(c[1] for c in constants)

namespace_value_lookup = {}
for c in constants:
    if c[0] not in namespace_value_lookup:
        namespace_value_lookup[c[0]] = set()
    namespace_value_lookup[c[0]].add(c[1])


common_namespaces = [c for c,_ in namespaces_counter.most_common(NUMBER_NAMESPACES)]

print(common_namespaces)
# quit()

ious = np.zeros((len(common_namespaces), len(common_namespaces)))

for c0 in common_namespaces:
    for c1 in common_namespaces:
        # compute intersection-over-union
        intersection = namespace_value_lookup[c0].intersection(namespace_value_lookup[c1])
        union = namespace_value_lookup[c0].union(namespace_value_lookup[c1])
        iou = len(intersection) / len(union)
        ious[common_namespaces.index(c0), common_namespaces.index(c1)] = iou

fig, ax = plt.subplots(figsize=(20,20))
cax = ax.matshow(ious, interpolation='nearest')
ax.grid(True)
plt.xticks(range(NUMBER_NAMESPACES), common_namespaces, rotation=90)
plt.yticks(range(NUMBER_NAMESPACES), common_namespaces)
fig.colorbar(cax, ticks=[0.0, 0.1, 0.2, 0.3, 0.4, 1])

# save the plot
plt.savefig('namespace-overlap.png')

# Print the most similar pairs
# get the indices of the most similar pairs
most_similar_pairs = []
for i, j in combinations(range(NUMBER_NAMESPACES), 2):
    if ious[i, j] > 0.1:
        most_similar_pairs.append((common_namespaces[i], common_namespaces[j], ious[i, j]))

for p in sorted(most_similar_pairs, key=lambda x: x[2], reverse=True):
    print(p)

# Print everything in Int that's not in Nat
print(namespace_value_lookup['Finset'].difference(namespace_value_lookup['List']))
