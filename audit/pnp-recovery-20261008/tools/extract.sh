#!/bin/bash
# Extract every unique Lean blob across all remote branches of a repo.
# Usage: extract.sh REPO_DIR OUT_DIR
set -u
repo=$1; out=$2
mkdir -p "$out/blobs"
git -C "$repo" for-each-ref --format='%(refname:short)' refs/remotes/origin | grep -v HEAD > "$out/refs.txt"
: > "$out/blobmap.tsv"
while read -r r; do
  git -C "$repo" ls-tree -r "$r" | awk -v r="$r" '$4 ~ /\.lean$/ {print $3"\t"r"\t"$4}' >> "$out/blobmap.tsv"
done < "$out/refs.txt"
cut -f1 "$out/blobmap.tsv" | sort -u > "$out/blobs.txt"
while read -r h; do git -C "$repo" cat-file -p "$h" > "$out/blobs/$h.lean"; done < "$out/blobs.txt"
echo "refs=$(wc -l < "$out/refs.txt") lean_files=$(wc -l < "$out/blobmap.tsv") unique_blobs=$(wc -l < "$out/blobs.txt")"
