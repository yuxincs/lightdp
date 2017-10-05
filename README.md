# LightDP

A Light-Weight imperative language for developing provably privacy-preserving algorithms.
More details can be found [here](http://www.cse.psu.edu/~dbz5017/pub/popl17.pdf).

This project presents a tool for transforming LightDP programs into Python programs along with differential-privacy proofs.

# Usage

To install it, run

```bash
$ python setup.py install
```

Then to transform LightDP program `source.ldp` to `output.py`, run

```bash
$ lightdp source.ldp -o output.py
```

This program can also run as a module like

```bash
$ python -m lightdp source.ldp -o output.py
```

Remember to check the requirement in `setup.py` if you do so.
