#!/usr/bin/env python3
import sys
import zulip
import re

# Usage:
# python scripts/zulip_emoji_merge_delegate.py $ZULIP_API_KEY $ZULIP_EMAIL $ZULIP_SITE $LABEL $PR_NUMBER
# See .github/workflows/zulip_emoji_merge_delegate.yaml for the meaning of these variables

ZULIP_API_KEY = sys.argv[1]
ZULIP_EMAIL = sys.argv[2]
ZULIP_SITE = sys.argv[3]
LABEL = sys.argv[4]
PR_NUMBER = sys.argv[5]

print(f"LABEL: '{LABEL}'")
print(f"PR_NUMBER: '{PR_NUMBER}'")

# Initialize Zulip client
client = zulip.Client(
    email=ZULIP_EMAIL,
    api_key=ZULIP_API_KEY,
    site=ZULIP_SITE
)

# Fetch the messages containing the PR number from the public channels.
# There does not seem to be a way to search simultaneously public and private channels.
public_response = client.get_messages({
    "anchor": "newest",
    "num_before": 5000,
    "num_after": 0,
    "narrow": [
        {"operator": "channels", "operand": "public"},
        {"operator": "search", "operand": f'#{PR_NUMBER}'},
    ],
})

# Fetch the messages containing the PR number from the `mathlib reviewers` channel
# There does not seem to be a way to search simultaneously public and private channels.
reviewers_response = client.get_messages({
    "anchor": "newest",
    "num_before": 5000,
    "num_after": 0,
    "narrow": [
        {"operator": "channel", "operand": "mathlib reviewers"},
        {"operator": "search", "operand": f'#{PR_NUMBER}'},
    ],
})

print(f"public_response:{public_response}")
print(f"reviewers_response:{reviewers_response}")

messages = (public_response['messages']) + (reviewers_response['messages'])

hashPR = re.compile(f'#{PR_NUMBER}')
urlPR = re.compile(f'https://github.com/leanprover-community/mathlib4/pull/{PR_NUMBER}')

print(f"Searching for: '{urlPR}'")

# we store in `first_by_subject` the ID of the messages in a thread whose subject matches
# the PR number and that we already visited. We use this to only react to the first message
# in each thread in `PR reviews` that matches the PR number.
first_by_subject = {}

for message in messages:
    if message['display_recipient'] == 'rss':
        continue
    content = message['content']
    # Check for emoji reactions
    reactions = message['reactions']
    # Does this message have any reaction with an emoji |name|?
    has_reaction = lambda name: any(reaction['emoji_name'] == name for reaction in reactions)

    has_peace_sign = has_reaction('peace_sign')
    has_bors = has_reaction('bors')
    has_merge = has_reaction('merge')
    has_awaiting_author = has_reaction('writing')
    has_maintainer_merge = has_reaction('hammer')
    has_closed = has_reaction('closed-pr')
    first_in_thread = hashPR.search(message['subject']) and message['display_recipient'] == 'PR reviews' and message['subject'] not in first_by_subject
    first_by_subject[message['subject']] = message['id']
    match = urlPR.search(content) or first_in_thread
    if match:
        print(f"matched: '{message}'")

        # Removing all previous emoji reactions.
        # If the emoji is a custom emoji, add the fields `emoji_code` and `reaction_type` as well.
        print("Removing previous reactions, if present.")
        def remove_reaction(name: str, emoji_name: str, **kwargs) -> None:
            print(f'Removing {name}')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": emoji_name,
                **kwargs
            })
            print(f"result: '{result}'")

        if has_peace_sign:
            remove_reaction('delegated', 'peace_sign')
        if has_bors:
            remove_reaction("bors", "bors", emoji_code="22134", reaction_type="realm_emoji")
        if has_merge:
            remove_reaction('merge', 'merge')
        if has_maintainer_merge:
            remove_reaction('maintainer-merge', 'hammer')
        if has_awaiting_author:
            remove_reaction('awaiting-author', 'writing')
        if has_closed:
            # 61282 was the earlier version of the emoji.
            remove_reaction('closed-pr', 'closed-pr', emoji_code="61293", reaction_type="realm_emoji")

        # applying appropriate emoji reaction
        print("Applying reactions, as appropriate.")
        def add_reaction(name: str, emoji_name: str) -> None:
            print(f'adding {name}')
            result = client.add_reaction({
                "message_id": message['id'],
                "emoji_name": emoji_name
            })
        if 'ready-to-merge' == LABEL:
            add_reaction('ready-to-merge', 'bors')
        elif 'delegated' == LABEL:
            add_reaction('delegated', 'peace_sign')
        elif 'maintainer-merge' == LABEL:
            add_reaction('maintainer-merge', 'hammer')
        elif LABEL == 'labeled':
            add_reaction('awaiting-author', 'writing')
        elif LABEL == 'closed':
            add_reaction('closed-pr', 'closed-pr')
        elif LABEL == 'unlabeled':
            print('awaiting-author removed')
            # The reaction was already removed.
        elif LABEL.startswith("[Merged by Bors]"):
            add_reaction('[Merged by Bors]', 'merge')
