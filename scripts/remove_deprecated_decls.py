import re
import sys
from datetime import datetime
from pathlib import Path

def is_date_older_than_cutoff(date_str, cutoff_str):
    """Check if date_str is older than cutoff_str (both YYYY-MM-DD format)"""
    try:
        date_obj = datetime.strptime(date_str, '%Y-%m-%d')
        cutoff_obj = datetime.strptime(cutoff_str, '%Y-%m-%d')
        return date_obj < cutoff_obj
    except ValueError:
        return False

def remove_old_deprecated_aliases(content, cutoff_date):
    """Remove deprecated aliases older than cutoff_date"""
    # Pattern to match deprecated aliases with expanded character set
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

def process_file(filepath, cutoff_date):
    """Process a single .lean file"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()

        new_content = remove_old_deprecated_aliases(content, cutoff_date)

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
    if len(sys.argv) != 2:
        print("Usage: python remove_deprecated.py CUTOFF_DATE", file=sys.stderr)
        sys.exit(1)

    cutoff_date = sys.argv[1]
    print(f"Removing deprecated aliases older than {cutoff_date}")

    # Find all .lean files in Mathlib directory
    mathlib_path = Path("Mathlib")
    if not mathlib_path.exists():
        print("Error: Mathlib directory not found", file=sys.stderr)
        sys.exit(1)

    processed_count = 0
    for lean_file in mathlib_path.rglob("*.lean"):
        if process_file(lean_file, cutoff_date):
            processed_count += 1

    print(f"Processed {processed_count} files")

if __name__ == "__main__":
    main()
