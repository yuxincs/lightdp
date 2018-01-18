import pytest
from lightdp.stattest import sampler, gauss, lapmech, nm


def test_prng():
    prng = sampler.Sampler('normal')
    prng2 = sampler.Sampler('laplace')
    assert isinstance(prng.laplace(0, 1), float)
    assert isinstance(prng2.laplace(0, 1), float)
    assert prng.weight() != 1
    assert prng2.weight() == 1
    assert isinstance(gauss.mech(1, 0, prng), float)
    assert isinstance(lapmech.mech(1, 0, prng), float)
    assert isinstance(nm.mech(1, [1.0, 2.0, 3.0], prng), float)
