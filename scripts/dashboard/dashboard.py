#!/usr/bin/env python3

# This script accepts json files as command line arguments and displays the data in an HTML dashboard

import sys
import json
from datetime import datetime
from dateutil import relativedelta

def main():
    # Check if the user has provided the correct number of arguments
    if len(sys.argv) < 2:
        print("Usage: python3 dashboard.py <json_file1> <json_file2> ...")
        sys.exit(1)

    print_html5_header()

    # Iterate over the json files provided by the user
    for i in range(1, len(sys.argv)):
        with open(sys.argv[i]) as f:
            data = json.load(f)
            print_dashboard(data)

    print_html5_footer()

def print_html5_header():
    print("""
    <!DOCTYPE html>
    <html>
    <head>
    <title>Mathlib Review Dashboard</title>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/jquery/3.5.1/jquery.min.js"
			integrity="sha512-bLT0Qm9VnAYZDflyKcBaQ2gg0hSYNQrJ8RilYldYQ1FxQYoCLtUjuuRuZo+fjqhx/qtq/1itJ0C2ejDxltZVFg=="
			crossorigin="anonymous"></script>
    <link rel="stylesheet" type="text/css" href="https://cdn.datatables.net/1.10.22/css/jquery.dataTables.css">
    <script type="text/javascript" charset="utf8" src="https://cdn.datatables.net/1.10.22/js/jquery.dataTables.js"></script>
    <link rel='stylesheet' href='style.css'>
    </head>
    <body>
    <h1>Mathlib Review Dashboard</h1>
    """)

def print_html5_footer():
    print("""
    <script>
    $(document).ready( function () {
        $('table').DataTable({
                pageLength: 25,
				"searching": false,
        });
    });
    </script>
    </body>
    </html>
    """)

# An HTML link to a mathlib PR
def pr_link(number, url):
    return "<a href='{}'>#{}</a>".format(url, number)

# An HTML link to a GitHub user profile
def user_link(author):
    login = author["login"]
    url   = author["url"]
    return "<a href='{}'>{}</a>".format(url, login)

# An HTML link to a Github label in the mathlib repo
def label_link(label):

    # Function to check if the colour of the label is light or dark
    # adapted from https://codepen.io/WebSeed/pen/pvgqEq
    def isLight(r, g, b):
        # Counting the perceptive luminance
        # human eye favors green color... 
        a = 1 - (0.299 * r + 0.587 * g + 0.114 * b) / 255
        return (a < 0.5)

    name  = label["name"]
    url   = label["url"]
    bgcolor = label["color"]
    fgcolor = "000000" if isLight(int(bgcolor[:2], 16), int(bgcolor[2:4], 16), int(bgcolor[4:], 16)) else "FFFFFF"
    s  = "<span class='label' style='color: #{}; background: #{}'>".format(fgcolor, bgcolor)
    s += "<a href='{}'>{}</a>".format(url, name)
    s += "</span>"
    return s

# Function to format the time of the last update
# Input is in the format: "2020-11-02T14:23:56Z"
# Output is in the format: "2020-11-02 14:23 (2 days ago)"
def time_info(updatedAt):
    updated = datetime.strptime(updatedAt, "%Y-%m-%dT%H:%M:%SZ")
    now = datetime.now()

    # Calculate the difference in time
    delta = relativedelta.relativedelta(now, updated)

    # Format the output
    s = updated.strftime("%Y-%m-%d %H:%M")
    if delta.years > 0:
        s += " ({} years ago)".format(delta.years)
    elif delta.months > 0:
        s += " ({} months ago)".format(delta.months)
    elif delta.days > 0:
        s += " ({} days ago)".format(delta.days)
    elif delta.hours > 0:
        s += " ({} hours ago)".format(delta.hours)
    elif delta.minutes > 0:
        s += " ({} minutes ago)".format(delta.minutes)
    else:
        s += " ({} seconds ago)".format(delta.seconds)

    return s

def print_dashboard(data):
    print("<h1>{}</h1>".format(data["title"]))
    print("<table>")
    print("<thead>")
    print("<tr>")
    print("<th>Number</th>")
    print("<th>Author</th>")
    print("<th>Labels</th>")
    print("<th>Updated</th>")
    print("</tr>")
    print("</thead>")

    # Iterate over the data and print each entry in a row
    for page in data["output"]:
        for entry in page["data"]["search"]["nodes"]:
            print("<tr>")
            print("<td>{}</td>".format(pr_link(entry["number"], entry["url"])))
            print("<td>{}</td>".format(user_link(entry["author"])))
            print("<td>")
            for label in entry["labels"]["nodes"]:
                print(label_link(label), end=' ')
            print("</td>")
            print("<td>{}</td>".format(time_info(entry["updatedAt"])))
            print("</tr>")

    # Print the footer
    print("</table>")

main()
