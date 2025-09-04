import re
import sys
from datetime import datetime
from pathlib import Path
import argparse

def is_date_older_than_cutoff(date_str, cutoff_str):
    """Check if date_str is older than cutoff_str (both YYYY-MM-DD format)"""
    try:
        date_obj = datetime.strptime(date_str, '%Y-%m-%d')
        cutoff_obj = datetime.strptime(cutoff_str, '%Y-%m-%d')
        return date_obj < cutoff_obj
    except ValueError:
        return False

def find_deprecated_declarations_to_remove(content, cutoff_date):
    """Find deprecated declarations that would be removed, returning list of matches"""
    pattern = r'@\[deprecated[^]]*since[^]]*"(\d{4}-\d{2}-\d{2})"[^]]*\]\s*(?:noncomputable\s+)?(?:protected\s+)?alias\s+[_a-zA-Zα-ωΑ-Ωϊ-ϻἀ-῾℀-⅏𝒜-𝖟\'.₀₁₂₃₄₅₆₇₈₉]*\s*:=\s*[_a-zA-Zα-ωΑ-Ωϊ-ϻἀ-῾℀-⅏𝒜-𝖟\'.₀₁₂₃₄₅₆₇₈₉]*'

    matches_to_remove = []
    for match in re.finditer(pattern, content, flags=re.MULTILINE | re.DOTALL):
        date_str = match.group(1)
        if is_date_older_than_cutoff(date_str, cutoff_date):
            # Find line numbers for this match
            lines_before = content[:match.start()].count('\n')
            start_line = lines_before + 1
            lines_in_match = match.group(0).count('\n')
            end_line = start_line + lines_in_match

            matches_to_remove.append({
                'text': match.group(0),
                'date': date_str,
                'start_line': start_line,
                'end_line': end_line,
                'start_pos': match.start(),
                'end_pos': match.end()
            })

    return matches_to_remove

def remove_old_deprecated_declarations(content, cutoff_date):
    """Remove deprecated declarations older than cutoff_date"""
    # Pattern to match deprecated declarations with expanded character set
    pattern = r'@\[deprecated[^]]*since[^]]*"(\d{4}-\d{2}-\d{2})"[^]]*\]\s*(?:noncomputable\s+)?(?:protected\s+)?alias\s+[_a-zA-Zα-ωΑ-Ωϊ-ϻἀ-῾℀-⅏𝒜-𝖟\'.₀₁₂₃₄₅₆₇₈₉]*\s*:=\s*[_a-zA-Zα-ωΑ-Ωϊ-ϻἀ-῾℀-⅏𝒜-𝖟\'.₀₁₂₃₄₅₆₇₈₉]*'

    def replacement_func(match):
        date_str = match.group(1)
        if is_date_older_than_cutoff(date_str, cutoff_date):
            return ''  # Remove the match
        else:
            return match.group(0)  # Keep the match

    # Apply the replacement
    content = re.sub(pattern, replacement_func, content, flags=re.MULTILINE | re.DOTALL)

    # Clean up consecutive blank lines (more than 2 consecutive newlines)
    content = re.sub(r'\n{3,}', '\n\n', content)

    return content

def process_file(filepath, cutoff_date, dry_run=False):
    """Process a single .lean file"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()

        if dry_run:
            # Find what would be removed
            matches_to_remove = find_deprecated_declarations_to_remove(content, cutoff_date)
            if matches_to_remove:
                print(f"\n{filepath}:")
                for i, match in enumerate(matches_to_remove, 1):
                    print(f"  Match {i} (lines {match['start_line']}-{match['end_line']}, date: {match['date']}):")
                    # Show the alias text with some context, truncated if too long
                    alias_text = match['text'].strip()
                    if len(alias_text) > 100:
                        alias_text = alias_text[:100] + "..."
                    print(f"    {alias_text}")
                return len(matches_to_remove)
            return 0
        else:
            # Actually perform the removal
            new_content = remove_old_deprecated_declarations(content, cutoff_date)

            # Only write if content changed
            if new_content != content:
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.write(new_content)
                print(f"Processed: {filepath}")
                return True
            return False
    except Exception as e:
        print(f"Error processing {filepath}: {e}", file=sys.stderr)
        return False

def main():
    parser = argparse.ArgumentParser(description='Remove deprecated declarations older than a specified date')
    parser.add_argument('cutoff_date', help='Cutoff date in YYYY-MM-DD format')
    parser.add_argument('--dry-run', action='store_true',
                       help='Show what would be removed without actually making changes')

    args = parser.parse_args()

    cutoff_date = args.cutoff_date
    dry_run = args.dry_run

    if dry_run:
        print(f"DRY RUN: Would remove deprecated declarations older than {cutoff_date}")
    else:
        print(f"Removing deprecated declarations older than {cutoff_date}")

    processed_count = 0
    total_matches = 0

    for directory in ["Mathlib", "Archive", "Counterexamples", "MathlibTest"]:
        # Find all .lean files in directory
        directory_path = Path(directory)
        if not directory_path.exists():
            print(f"Error: {directory} directory not found", file=sys.stderr)
            sys.exit(1)

        print(f"::group::checking {directory}")

        for lean_file in directory_path.rglob("*.lean"):
            result = process_file(lean_file, cutoff_date, dry_run)
            if dry_run:
                if result > 0:
                    processed_count += 1
                    total_matches += result
            else:
                if result:
                    processed_count += 1

        print(f"::endgroup::")

    if dry_run:
        print(f"\nDRY RUN SUMMARY:")
        print(f"Found {total_matches} deprecated declarations to remove in {processed_count} files")
    else:
        print(f"Processed {processed_count} files")

if __name__ == "__main__":
    main()
