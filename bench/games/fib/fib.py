a, b = 0, 1
for _ in range(30):
    a, b = b, a + b
print(a)
