import json
import unittest
from unittest.mock import patch

from guard import (
    API,
    LABEL,
    MARKER,
    REPO,
    SITE,
    Guard,
    MutationFailed,
    Unavailable,
    Zulip,
    decode_topic,
    directive,
    labeler,
    references_pr,
    request_comment,
    zulip_urls,
)

NUMBER = 12345
PR_URL = f"https://github.com/{REPO}/pull/{NUMBER}"
TOPIC_URL = SITE + "/#narrow/channel/287929-mathlib4/topic/Example/with/10"


def message(content="", **kwargs):
    return {"content": content, "subject": "Example", **kwargs}


def link(url, text="this PR"):
    return f'<p><a href="{url}">{text}</a></p>'


class ReferenceTests(unittest.TestCase):
    def test_full_urls_and_expanded_linkifiers(self):
        for text in (
            PR_URL,
            "#12345",
            "mathlib4#12345",
            "mathlib#12345",
            "a description",
        ):
            with self.subTest(text=text):
                self.assertTrue(references_pr(message(link(PR_URL, text)), NUMBER))
        for suffix in (
            "#issuecomment-123",
            "?foo=1&amp;bar=2",
            "/",
            "/files",
            "/commits/abcd",
        ):
            self.assertTrue(references_pr(message(link(PR_URL + suffix)), NUMBER))
        self.assertTrue(
            references_pr(message(link(PR_URL.replace("/pull/", "/issues/"))), NUMBER)
        )

    def test_linkifiers_and_full_urls_in_topic(self):
        for field in ("topic_links", "subject_links"):
            self.assertTrue(
                references_pr(
                    message(**{field: [{"url": PR_URL, "text": "#12345"}]}), NUMBER
                )
            )
        self.assertTrue(references_pr(message(subject="Discussion " + PR_URL), NUMBER))

    def test_wrong_repo_number_and_misleading_links(self):
        for url in (
            PR_URL + "6",
            PR_URL + "abc",
            PR_URL.replace("mathlib4", "lean4"),
            PR_URL.replace("leanprover-community/mathlib4", "leanprover/lean4"),
            PR_URL.replace("github.com", "github.com.evil.example"),
            PR_URL.replace("github.com", "github.com@evil.example"),
            PR_URL.replace("github.com", "evil.example/github.com"),
        ):
            with self.subTest(url=url):
                self.assertFalse(references_pr(message(link(url, "#12345")), NUMBER))

    def test_bare_numbers_and_code_are_not_references(self):
        for content in ("<p>12345</p>", "<code>#12345</code>", "<p>lean#12345</p>"):
            self.assertFalse(references_pr(message(content), NUMBER))

    def test_extracts_only_specific_zulip_links(self):
        texts = [
            f"[discussion]({TOPIC_URL}).",
            f'<a href="{TOPIC_URL}">topic</a>',
            SITE,
            SITE + "/#narrow/channel/287929-mathlib4",
            "https://evil.example/" + TOPIC_URL,
            SITE + ".evil.example/#narrow/channel/1-x/topic/Example",
        ]
        self.assertEqual(zulip_urls(texts), [TOPIC_URL])
        old = SITE + "/#narrow/stream/287929-mathlib4/topic/Example"
        self.assertEqual(zulip_urls([old]), [old])

    def test_zulip_topic_encoding(self):
        self.assertEqual(decode_topic("Type.20.60.CE.B1.60.2E"), "Type `α`.")
        self.assertEqual(decode_topic("Type%20.CE.B1"), "Type α")

    def test_directive_syntax_and_review_bodies(self):
        self.assertEqual(
            directive("awaiting-zulip\r\n -awaiting-zulip\r\n"), "-" + LABEL
        )
        self.assertEqual(directive("  awaiting-zulip \n"), LABEL)
        for text in (
            "please awaiting-zulip",
            "`awaiting-zulip`",
            "- awaiting-zulip",
            "!other awaiting-zulip",
        ):
            self.assertIsNone(directive(text))
        self.assertEqual(request_comment({"review": {"body": LABEL}})["body"], LABEL)


class TopicAPI:
    def __init__(self):
        self.calls = []

    def call(self, path, *, params=None):
        self.calls.append((path, params))
        if path.startswith("/messages/"):
            return {
                "message": {
                    "type": "stream",
                    "stream_id": 99,
                    "subject": "Renamed topic",
                }
            }
        if params["anchor"] == "oldest":
            return {
                "messages": [{"id": 1, **message("unrelated")}],
                "found_newest": False,
            }
        return {"messages": [{"id": 2, **message(link(PR_URL))}], "found_newest": True}


class TopicTests(unittest.TestCase):
    def test_resolves_anchor_and_checks_entire_topic(self):
        api = TopicAPI()
        zulip = Zulip(api)
        self.assertTrue(zulip.qualifies([TOPIC_URL], NUMBER))
        narrow = json.loads(api.calls[1][1]["narrow"])
        self.assertEqual(
            narrow,
            [
                {"operator": "channel", "operand": 99},
                {"operator": "topic", "operand": "Renamed topic"},
            ],
        )
        self.assertEqual(len(api.calls), 3)
        self.assertTrue(
            zulip.qualifies([TOPIC_URL.replace("/with/", "/near/")], NUMBER)
        )
        self.assertEqual(len(api.calls), 3)  # Cache canonical topic and anchor.

    def test_topic_only_and_legacy_channel_links(self):
        zulip = Zulip(TopicAPI())
        self.assertEqual(
            zulip.topic(SITE + "/#narrow/stream/99-test/topic/A.20B"), (99, "A B")
        )

    def test_inaccessible_links_preserve_label_unless_other_link_qualifies(self):
        zulip = Zulip(TopicAPI())
        original = zulip.topic

        def topic(url):
            if url == "unavailable":
                raise Unavailable("inaccessible")
            return original(url)

        zulip.topic = topic
        with self.assertRaises(Unavailable):
            zulip.qualifies(["unavailable"], NUMBER)
        self.assertTrue(zulip.qualifies(["unavailable", TOPIC_URL], NUMBER))

    def test_incomplete_pagination_is_inconclusive(self):
        api = TopicAPI()
        api.call = lambda *args, **kwargs: {"messages": [], "found_newest": False}
        with self.assertRaises(Unavailable):
            Zulip(api).messages((99, "Example"))


class FakeGitHub:
    def __init__(self, *, present=True):
        self.issue = {
            "state": "open",
            "pull_request": {},
            "body": "",
            "labels": [{"name": LABEL}] if present else [],
        }
        self.issue_comments = []
        self.reviews = []
        self.inline = []
        self.events = [
            {
                "id": 1,
                "event": "labeled",
                "label": {"name": LABEL},
                "actor": {"login": "labeler", "type": "User"},
                "created_at": "2026-10-21T10:00:00Z",
            }
        ]
        self.writes = []

    def pages(self, path):
        if path.endswith("/events"):
            return list(self.events)
        if path.endswith("/reviews"):
            return self.reviews
        if "/pulls/" in path:
            return self.inline
        return self.issue_comments

    def call(self, path, *, method="GET", data=None):
        if method == "GET":
            return self.issue
        self.writes.append((method, path, data))


class FakeZulip:
    def __init__(self, valid=False, error=False):
        self.valid = valid
        self.error = error
        self.urls = []

    def qualifies(self, urls, number):
        self.urls = urls
        if self.error:
            raise Unavailable("outage")
        return self.valid


class EnforcementTests(unittest.TestCase):
    def test_removes_missing_label_and_mentions_labeler(self):
        gh = FakeGitHub()
        Guard(gh, FakeZulip()).check(NUMBER)
        self.assertEqual([w[0] for w in gh.writes], ["DELETE", "POST"])
        body = gh.writes[-1][2]["body"]
        self.assertIn("@labeler, thanks", body)
        self.assertIn("#12345", body)
        self.assertIn("reapply", body)
        self.assertIn("I’ve removed", body)

    def test_declines_invalid_directive_but_applies_valid_directive(self):
        for valid in (True, False):
            gh = FakeGitHub(present=False)
            Guard(gh, FakeZulip(valid)).check(NUMBER, command=LABEL, author="requester")
            self.assertEqual(len(gh.writes), 1)
            if valid:
                self.assertEqual(gh.writes[0][2], {"labels": [LABEL]})
            else:
                self.assertIn("@requester", gh.writes[0][2]["body"])
                self.assertIn("haven’t applied", gh.writes[0][2]["body"])

    def test_no_mutations_on_outage_or_dry_run(self):
        gh = FakeGitHub()
        with self.assertRaises(Unavailable):
            Guard(gh, FakeZulip(error=True)).check(NUMBER)
        self.assertEqual(gh.writes, [])
        Guard(gh, FakeZulip(), dry_run=True).check(NUMBER)
        self.assertEqual(gh.writes, [])

    def test_reads_description_review_and_inline_links(self):
        gh = FakeGitHub()
        gh.issue["body"] = TOPIC_URL
        gh.issue_comments = [{"body": TOPIC_URL.replace("10", "11")}]
        gh.reviews = [{"body": TOPIC_URL.replace("10", "12")}]
        gh.inline = [{"body": TOPIC_URL.replace("10", "13")}]
        zulip = FakeZulip(valid=True)
        Guard(gh, zulip).check(NUMBER)
        self.assertEqual(len(zulip.urls), 4)
        self.assertEqual(gh.writes, [])

    def test_updates_own_notice_but_never_another_users_comment(self):
        gh = FakeGitHub()
        gh.issue_comments = [
            {"id": 6, "body": MARKER, "user": {"login": "human"}},
            {"id": 7, "body": MARKER, "user": {"login": "github-actions[bot]"}},
        ]
        Guard(gh, FakeZulip()).check(NUMBER)
        self.assertEqual(gh.writes[-1][0], "PATCH")
        self.assertTrue(gh.writes[-1][1].endswith("/7"))

    def test_never_removes_a_new_label_lifecycle(self):
        gh = FakeGitHub()
        zulip = FakeZulip()

        def changed(urls, number):
            gh.events.append({**gh.events[0], "id": 2})
            return False

        zulip.qualifies = changed
        Guard(gh, zulip).check(NUMBER)
        self.assertEqual(gh.writes, [])

    def test_defers_if_pr_changes_during_verification(self):
        gh = FakeGitHub()
        gh.issue["updated_at"] = "before"
        original = gh.call

        def changed(path, **kwargs):
            result = original(path, **kwargs)
            return dict(result) if result else result

        gh.call = changed
        zulip = FakeZulip()

        def update(urls, number):
            gh.issue["updated_at"] = "after"
            return False

        zulip.qualifies = update
        Guard(gh, zulip).check(NUMBER)
        self.assertEqual(gh.writes, [])

    def test_removal_does_not_require_zulip(self):
        gh = FakeGitHub()
        Guard(gh, FakeZulip(error=True)).check(NUMBER, command="-" + LABEL)
        self.assertEqual([w[0] for w in gh.writes], ["DELETE"])

    def test_closed_prs_and_ordinary_issues_are_ignored(self):
        gh = FakeGitHub()
        gh.issue["state"] = "closed"
        Guard(gh, FakeZulip(error=True)).check(NUMBER)
        gh.issue["state"] = "open"
        del gh.issue["pull_request"]
        Guard(gh, FakeZulip(error=True)).check(NUMBER)
        self.assertEqual(gh.writes, [])

    def test_historical_bot_label_is_attributed_to_directive_author(self):
        applied = {
            "actor": {"login": "github-actions[bot]", "type": "Bot"},
            "created_at": "2026-10-21T10:00:00Z",
        }
        comments = [
            {
                "body": LABEL,
                "created_at": "2026-10-21T09:50:00Z",
                "user": {"login": "human", "type": "User"},
            },
            {
                "body": "unrelated",
                "created_at": "2026-10-21T09:59:59Z",
                "user": {"login": "other", "type": "User"},
            },
        ]
        self.assertEqual(labeler(applied, comments), "human")


class APITests(unittest.TestCase):
    def test_paginates_github_comments(self):
        api = API("https://api.github.com", "Bearer unused")
        api.call = lambda path, params: [None] * (100 if params["page"] == 1 else 3)
        self.assertEqual(len(api.pages("/comments")), 103)

    def test_retries_reads_but_not_comment_creation(self):
        from urllib.error import URLError

        api = API("https://api.github.com", "Bearer unused")
        with (
            patch.object(api.opener, "open", side_effect=URLError("offline")) as opened,
            patch("guard.time.sleep"),
        ):
            with self.assertRaises(Unavailable):
                api.call("/test")
            self.assertEqual(opened.call_count, 3)
            opened.reset_mock()
            with self.assertRaises(MutationFailed):
                api.call("/comments", method="POST", data={"body": "text"})
            self.assertEqual(opened.call_count, 1)


if __name__ == "__main__":
    unittest.main()
