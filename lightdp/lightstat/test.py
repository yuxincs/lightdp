import sampler
import gauss
import lapmech
import nm

prng = sampler.Sampler('normal')

print (gauss.mech(1,0,prng))

print (prng.weight)

print (lapmech.mech(1,0,prng))

print (prng.weight)


x = [1.0, 2.0, 3.0]

print (nm.mech(1,x,prng))