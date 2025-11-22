# Aristotle API Integration for Mathlib

This directory contains configuration for integrating Aristotle's automated theorem proving API with Mathlib.

## What is Aristotle?

Aristotle is an automated theorem proving service that can generate Lean proofs. It accepts Lean files with theorem statements and returns completed proofs. Learn more at [aristotle.harmonic.fun](https://aristotle.harmonic.fun).

## Quick Start

### 1. Install aristotlelib

Install or upgrade to the latest version (requires version 0.4.0 or later for CLI support):

```bash
pip install --upgrade aristotlelib
```

If you're using a system Python, you may need:

```bash
pip install --upgrade aristotlelib --break-system-packages
```

This provides both a Python API and a command-line interface.

### 2. Set Your API Key

Configure your Aristotle API key using an environment variable:

```bash
export ARISTOTLE_API_KEY='your-api-key-here'
```

To make this permanent, add it to your `~/.bashrc` or `~/.zshrc`:

```bash
echo "export ARISTOTLE_API_KEY='your-api-key-here'" >> ~/.bashrc
source ~/.bashrc
```

### 3. Use the Tool

#### From VSCode

1. Open any `.lean` file
2. Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on macOS)
3. Type "Tasks: Run Task"
4. Select "Aristotle: Prove Current File"

The proof will be generated in the same directory with a `_aristotle.lean` suffix.

Alternatively, select "Aristotle: Prove Current File (Custom Output)" to specify a custom output path.

#### From Command Line

```bash
# Basic usage - generates output in the same directory with _aristotle suffix
aristotle prove-from-file Mathlib/Analysis/Deriv.lean

# Custom output location
aristotle prove-from-file Mathlib/Analysis/Deriv.lean --output-file MyProof.lean

# Show help and all available options
aristotle prove-from-file --help
```

## Output Files

By default, when you run the tool on a file `X/Y.lean`, it creates `X/Y_aristotle.lean` with the generated proof.

## Additional Resources

For complete documentation on the aristotlelib CLI and Python API, visit [pypi.org/project/aristotlelib](https://pypi.org/project/aristotlelib/).
