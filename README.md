`stridi` is a Haskell library and DSL to render string diagrams in LaTeX using TikZ.

- `StriDi.Cells` provides statically typed datastructures to represent 2-cells in an arbitrary bicategory;
- `StriDi.Render` provides function to render a 2-cell into TikZ code;
- `StriDi.DSL` provides submodules with DSLs to help defining such 2-cells. So far there is a DSL for monoidal categories and one for PROPs.

Apologies for the drastic lack of documentation; look at `test.hs` for an example usage of the library.

To build it, the easiest is using nix:
```bash
nix-build project.stridi.components.library
```
But then I'm not sure how to use the output without nix x)

To hack on it, just run `nix-shell`, and build with `cabal build`. This project uses haskell.nix.

Todo:
- include sample output in README
- fix some rendering quirks
- define invariants for the rendering process
- tests for the rendering pipeline ?
- make typechecker errors actually useful/readable
- display typechecker error in nicely rendered LaTeX ?
- color 0-cells to support bicategories fully
- DSL for bicategories
- per-2cell config of dimensions
- create an external (text) DSL to avoid having to compile Haskell over and over
- add pretty-printing of cell formula and cell type

Contributions and ideas are more than welcome !
