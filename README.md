# LightDP
[![Build Status](https://travis-ci.com/RyanWangGit/lightdp.svg?branch=master)](https://travis-ci.com/RyanWangGit/lightdp)

A Light-Weight imperative language for developing provably privacy-preserving algorithms.
More details can be found [here](http://www.cse.psu.edu/~dbz5017/pub/popl17.pdf).

This project presents a tool for transforming LightDP programs into Python programs along with differential-privacy proofs.

# Install

To install it, run

```bash
$ python setup.py install
```

or use 

```bash
$ python setup.py develop
```

for dependencies installation without installing the program into system.

This program needs `z3` and the corresponding python bindings installed in the system, check [z3's webpage](https://github.com/Z3Prover/z3) for installation instructions. 

A simple script `scripts/install_z3.py` is provided for easy installation of `z3`. Which collects the library from the [`z3`'s release page](https://github.com/Z3Prover/z3/releases) and installs at the current directory. An argument can be provided to the script to install the library and python bindings elsewhere, note that this does not install `z3` into the system.

# Usage

The original python program 
To transform LightDP-annotated program `source.py` to `output.py`, run

```bash
$ lightdp source.py -o output.py
```

If `-o` is not given the default output file name is `source_t.py`.

This program can also run as a module like

```bash
$ python -m lightdp source.ldp -o output.py
```

# Examples

Examples can be found at `./examples`, currently `sparse_vector.py` and `sparse_vector_t.py` is included.