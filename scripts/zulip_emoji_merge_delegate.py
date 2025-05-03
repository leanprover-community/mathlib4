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
    has_peace_sign = any(reaction['emoji_name'] == 'peace_sign' for reaction in reactions)
    has_bors = any(reaction['emoji_name'] == 'bors' for reaction in reactions)
    has_merge = any(reaction['emoji_name'] == 'merge' for reaction in reactions)
    has_awaiting_author = any(reaction['emoji_name'] == 'writing' for reaction in reactions)
    has_maintainer_merge = any(reaction['emoji_name'] == 'hammer' for reaction in reactions)
    has_closed = any(reaction['emoji_name'] == 'closed-pr' for reaction in reactions)
    first_in_thread = hashPR.search(message['subject']) and message['display_recipient'] == 'PR reviews' and message['subject'] not in first_by_subject
    first_by_subject[message['subject']] = message['id']
    match = urlPR.search(content) or first_in_thread
    if match:
        print(f"matched: '{message}'")

        # removing previous emoji reactions
        # if the emoji is a custom emoji, add the fields `emoji_code` and `reaction_type` as well
        print("Removing previous reactions, if present.")
        if has_peace_sign:
            print('Removing peace_sign')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "peace_sign"
            })
            print(f"result: '{result}'")
        if has_bors:
            print('Removing bors')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "bors",
                "emoji_code": "22134",
                "reaction_type": "realm_emoji",
            })
            print(f"result: '{result}'")
        if has_merge:
            print('Removing merge')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "merge"
            })
            print(f"result: '{result}'")
        if has_maintainer_merge:
            print('Removing maintainer-merge')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "hammer"
            })
            print(f"result: '{result}'")
        if has_awaiting_author:
            print('Removing awaiting-author')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "writing"
            })
            print(f"result: '{result}'")
        if has_closed:
            print('Removing closed-pr')
            result = client.remove_reaction({
                "message_id": message['id'],
                "emoji_name": "closed-pr",
                "emoji_code": "61293",  # 61282 was the earlier version of the emoji
                "reaction_type": "realm_emoji",
            })
            print(f"result: '{result}'")


        # applying appropriate emoji reaction
        print("Applying reactions, as appropriate.")
        if 'ready-to-merge' == LABEL:
            print('adding ready-to-merge')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "bors"
            })
        elif 'delegated' == LABEL:
            print('adding delegated')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "peace_sign"
            })
        elif 'maintainer-merge' == LABEL:
            print('adding maintainer-merge')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "hammer"
            })
        elif LABEL == 'labeled':
            print('adding awaiting-author')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "writing"
            })
        elif LABEL == 'closed':
            print('adding closed-pr')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "closed-pr"
            })
        elif LABEL == 'unlabeled':
            print('awaiting-author removed')
            # the reaction was already removed.
        elif LABEL.startswith("[Merged by Bors]"):
            print('adding [Merged by Bors]')
            client.add_reaction({
                "message_id": message['id'],
                "emoji_name": "merge"
            })
