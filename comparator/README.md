# Comparator Setup

This directory contains the Comparator configuration for the public paper
statements in `Erdos1196.lean`.

- `Challenge.lean` restates the seven public result statements using the
  `Erdos1196` namespace.
- `Erdos1196.lean` is the solution module checked against those statements.
- `comparator/config.json` lists the checked theorem names and permits only
  `propext`, `Classical.choice`, and `Quot.sound`.

With `comparator`, `landrun`, and `lean4export` available as described in
the upstream Comparator README, run from the repository root:

```bash
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" -- \
  bash -c 'lake env comparator comparator/config.json'
```
