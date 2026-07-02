# hofold.py — Python reference for the higher-order fold benchmark (P10). Applies a closure to an
# accumulator 10^6 times; each call is an indirect (dynamic) dispatch, the same shape Blight's
# bl_app closure apply has. Prints 1000000.

def adder(k):
    return lambda a: a + k

def iterate(fuel, step, acc):
    for _ in range(fuel):
        acc = step(acc)
    return acc

print(iterate(1000000, adder(1), 0))
