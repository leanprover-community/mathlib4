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

def find_deprecated_blocks_to_remove(content, cutoff_date):
    """Find blocks containing deprecated declarations that would be removed"""
    # Find block boundaries (blank lines)
    block_separators = list(re.finditer(r'\n\s*\n', content))

    # Define block boundaries
    block_starts = [0] + [match.end() for match in block_separators]
    block_ends = [match.start() for match in block_separators] + [len(content)]

    blocks_to_remove = []

    for i, (start, end) in enumerate(zip(block_starts, block_ends)):
        block_content = content[start:end]

        # Find all deprecated attributes with dates in this block
        deprecated_matches = list(re.finditer(r'@\[deprecated[^]]*since[^]]*"(\d{4}-\d{2}-\d{2})"[^]]*\]', block_content))

        if deprecated_matches:
            # Check if any deprecated declaration in this block is older than cutoff
            should_remove = False
            oldest_date = None

            for match in deprecated_matches:
                date_str = match.group(1)
                if is_date_older_than_cutoff(date_str, cutoff_date):
                    should_remove = True
                    if oldest_date is None or date_str < oldest_date:
                        oldest_date = date_str

            if should_remove:
                # Find line numbers for this block
                lines_before = content[:start].count('\n')
                start_line = lines_before + 1
                lines_in_block = block_content.count('\n')
                end_line = start_line + lines_in_block

                blocks_to_remove.append({
                    'block_index': i,
                    'start_pos': start,
                    'end_pos': end,
                    'text': block_content,
                    'oldest_date': oldest_date,
                    'start_line': start_line,
                    'end_line': end_line,
                    'deprecated_count': len(deprecated_matches)
                })

    return blocks_to_remove

def remove_old_deprecated_blocks(content, cutoff_date):
    """Remove blocks containing deprecated declarations older than cutoff_date"""
    # Find blocks to remove
    blocks_to_remove = find_deprecated_blocks_to_remove(content, cutoff_date)

    if not blocks_to_remove:
        # No changes needed
        return content

    # Sort blocks by start position in reverse order for safe removal
    blocks_to_remove.sort(key=lambda x: x['start_pos'], reverse=True)

    # Remove blocks from the content
    new_content = content
    for block_info in blocks_to_remove:
        start_pos = block_info['start_pos']
        end_pos = block_info['end_pos']

        # Check if we need to clean up separators around the removed block
        before_text = new_content[:start_pos]
        after_text = new_content[end_pos:]

        # Look for blank line patterns before and after
        before_has_blank = before_text.endswith('\n\n') or before_text.endswith('\n\t\n') or before_text.endswith('\n \n')
        after_starts_blank = after_text.startswith('\n\n') or after_text.startswith('\n\t\n') or after_text.startswith('\n \n')

        # Remove the block
        new_content = before_text + after_text

        # Handle separator cleanup to avoid multiple blank lines
        if before_has_blank and after_starts_blank:
            # We now have content ending with blank line + content starting with blank line
            # This creates too much separation, so we need to normalize

            # Find the end of the "before" content (last non-whitespace)
            before_content_end = len(before_text.rstrip())

            # Find the start of the "after" content (first non-whitespace)
            after_content_start = len(after_text) - len(after_text.lstrip())

            if before_content_end > 0 and after_content_start < len(after_text):
                # We have content both before and after, ensure exactly one blank line
                clean_before = before_text.rstrip()
                clean_after = after_text.lstrip()
                new_content = clean_before + '\n\n' + clean_after

    return new_content

def process_file(filepath, cutoff_date, dry_run=False):
    """Process a single .lean file"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()

        if dry_run:
            # Find what would be removed
            blocks_to_remove = find_deprecated_blocks_to_remove(content, cutoff_date)
            if blocks_to_remove:
                print(f"\n{filepath}:")
                for i, block_info in enumerate(blocks_to_remove, 1):
                    print(f"  Block {i} (lines {block_info['start_line']}-{block_info['end_line']}, oldest date: {block_info['oldest_date']}, {block_info['deprecated_count']} deprecated items):")
                    # Show first few lines of the block
                    block_lines = block_info['text'].strip().split('\n')
                    preview_lines = block_lines[:3]  # Show first 3 lines
                    if len(block_lines) > 3:
                        preview_lines.append("...")
                    for line in preview_lines:
                        print(f"    {line}")
                return len(blocks_to_remove)
            return 0
        else:
            # Actually perform the removal
            new_content = remove_old_deprecated_blocks(content, cutoff_date)

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
        print(f"Found {total_matches} deprecated blocks to remove in {processed_count} files")
    else:
        print(f"Processed {processed_count} files")

if __name__ == "__main__":
    main()
