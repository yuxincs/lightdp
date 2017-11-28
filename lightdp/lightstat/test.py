import sampler
import gauss
import lapmech
import nm

prng = sampler.Sampler('normal')

prng2 = sampler.Sampler('laplace')

print (prng2.laplace(0,1))

print (prng2.normal(0,1))

print (gauss.mech(1,0,prng))

print (prng.weight)

print (lapmech.mech(1,0,prng))

print (prng.weight)


x = [1.0, 2.0, 3.0]

print (nm.mech(1,x,prng))