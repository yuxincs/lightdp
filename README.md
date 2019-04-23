# LightDP
[![Build Status](https://travis-ci.com/RyanWangGit/lightdp.svg?branch=master)](https://travis-ci.com/RyanWangGit/lightdp) [![codecov](https://codecov.io/gh/RyanWangGit/lightdp/branch/master/graph/badge.svg)](https://codecov.io/gh/RyanWangGit/lightdp)

A Light-Weight imperative language for developing provably privacy-preserving algorithms.
More details can be found in the [paper](http://www.cse.psu.edu/~dbz5017/pub/popl17.pdf).

This project presents a tool for transforming LightDP programs into Python programs along with differential-privacy proofs, it is built to learn the ideas of LightDP and very primitive.

# Install

Virtual environment is highly recommended (or if you prefer `virtualenv` or `conda`, the setup is similar):
```bash
python -m venv venv
source venv/bin/acitvate
# now we're in virtual environment
pip install .
```

# Usage

```bash
usage: lightdp [-h] [-o OUT] [-c CONSTRAINTS] FILE

positional arguments:
  FILE

optional arguments:
  -h, --help            show this help message and exit
  -o OUT, --out OUT     The output file name.
  -c CONSTRAINTS, --constraints CONSTRAINTS
                        Output all constraints to file.
```

For example, run `lightdp ./examples/sparsevector.py` for verifying Sparse Vector, `LightDP` will output:
```
2019-04-23 10:58:35 INFO Type check succeeds, now transforming the algorithm...
2019-04-23 10:58:35 INFO Transformation finished at ./sparse_vector_t.py. See ./sparse_vector_constraints.txt for constraints generated.
```
. We also put some annotated programs in `examples/` for references. The default name for transformed file and constraint file is `*_t.py` and `*_constraints.txt`.
