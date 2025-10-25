# Aristotle API Integration for Mathlib

This directory contains tools for integrating Aristotle's automated theorem proving API with Mathlib.

## What is Aristotle?

Aristotle is an automated theorem proving service that can generate Lean proofs. It accepts Lean files with theorem statements and returns completed proofs. Learn more at [aristotle.harmonic.fun](https://aristotle.harmonic.fun).

## Quick Start

### 1. Install aristotlelib

```bash
pip install aristotlelib
```

### 2. Set Your API Key

You can configure your Aristotle API key in three ways (in priority order):

#### Option A: Project Config File (Recommended for Mathlib contributors)

Create a `.aristotle.conf` file in the repository root:

```bash
cp .aristotle.conf.example .aristotle.conf
# Edit .aristotle.conf and add your API key
```

Or directly:

```bash
echo "ARISTOTLE_API_KEY=your-api-key-here" > .aristotle.conf
```

This file is git-ignored, so your key won't be committed.

#### Option B: User Config File (Recommended for personal use)

Create a config file in your home directory:

```bash
mkdir -p ~/.config/aristotle
echo "ARISTOTLE_API_KEY=your-api-key-here" > ~/.config/aristotle/config
```

This works across all projects.

#### Option C: Environment Variable

Set the environment variable:

```bash
export ARISTOTLE_API_KEY='your-api-key-here'
```

To make this permanent, add it to your `~/.bashrc`:

```bash
echo "export ARISTOTLE_API_KEY='your-api-key-here'" >> ~/.bashrc
source ~/.bashrc
```

**Note:** Environment variables take precedence over config files.

### 3. Use the Tool

#### From Command Line

```bash
# Basic usage - generates Mathlib/Analysis/Deriv_aristotle.lean
python3 scripts/aristotle/prove.py Mathlib/Analysis/Deriv.lean

# Custom output location
python3 scripts/aristotle/prove.py Mathlib/Analysis/Deriv.lean --output MyProof.lean

# Show help
python3 scripts/aristotle/prove.py --help
```

#### From VSCode

1. Open any `.lean` file
2. Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on macOS)
3. Type "Tasks: Run Task"
4. Select "Aristotle: Prove Current File"

The proof will be generated in the same directory with a `_aristotle.lean` suffix.

## Output Files

By default, when you run the tool on a file `X/Y.lean`, it creates `X/Y_aristotle.lean` with the generated proof.
