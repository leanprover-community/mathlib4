set -e
set -x

git config --global user.email "leanprover.community@gmail.com"
git config --global user.name "leanprover-community-bot"

cd mathlib4
mathlib_short_git_hash="$(git log -1 --pretty=format:%h)"
cd ../

git clone --depth 1 "https://github.com/leanprover-community/mathlib4_docs.git" mathlib4_docs

# Workaround for the lake issue
elan default leanprover/lean4:nightly
lake new workaround
cd workaround
cp -f ../mathlib4/lean-toolchain .
echo 'require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"' >> lakefile.lean
echo 'require «mathlib» from ".." / "mathlib4"' >> lakefile.lean

# doc-gen4 expects to work on github repos with at least one commit
git add .
git commit -m "workaround"
git remote add origin "https://github.com/leanprover/workaround"

mkdir lake-packages
cp -r ../mathlib4/lake-packages/* lake-packages/
lake update

cd lake-packages/doc-gen4
doc_gen_short_git_hash="$(git log -1 --pretty=format:%h)"
cd ../../

if [ "$(cd ../mathlib4_docs && git log -1 --pretty=format:%s)" == "automatic update to mathlib4 $mathlib_short_git_hash using doc-gen4 $doc_gen_short_git_hash" ]; then
  exit 0
fi

lake build Std:docs Qq:docs Mathlib:docs Archive:docs Counterexamples:docs docs:docs

cd ..
rm -rf mathlib4_docs/docs/
cp -r "workaround/build/doc" mathlib4_docs/docs
cp mathlib4/docs/{100.yaml,overview.yaml,undergrad.yaml} mathlib4_docs/docs
ssh_key=$PWD/deploy_key
echo "$MATHLIB4_DOCS_KEY" > $ssh_key
chmod 600 $ssh_key
mkdir -p ~/.ssh; ssh-keyscan github.com >~/.ssh/known_hosts
ssh -i $ssh_key git@github.com || true # check ssh access
cd mathlib4_docs/docs
git remote set-url origin "git@github.com:leanprover-community/mathlib4_docs.git"
git add -A .
git checkout --orphan master2
git commit -m "automatic update to mathlib4 $mathlib_short_git_hash using doc-gen4 $doc_gen_short_git_hash"
GIT_SSH_COMMAND="ssh -i $ssh_key" git push -f origin HEAD:master
rm $ssh_key
