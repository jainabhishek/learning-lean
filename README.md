# learning-lean

## Getting started

Install Lean (via `elan`) and add it to your PATH if needed:

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.zprofile
source ~/.zprofile
```

Build and run:

```sh
lake build
lake exe learning-lean
```

## VS Code

Install the Lean 4 extension:
https://marketplace.visualstudio.com/items?itemName=leanprover.lean4

Open the folder and check `Main.lean`; the Lean Infoview shows goals and evals.
