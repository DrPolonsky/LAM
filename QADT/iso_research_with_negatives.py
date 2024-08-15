import re
def main():
    diff = [-1, -2, -1]
    poly = [0, 1, 0, 0, 0]
    last = poly
    with open("poly_log.txt", "w") as log:
        while True:
            if poly != last: log.write(" | ".join(map(lambda x: f"{x:3d}", poly)) + "\n")
            print(" | ".join(map(lambda x: f"{x:3d}", range(len(poly)))))
            print(" | ".join(map(lambda x: f"{x:3d}", poly)))
            last = poly[:]
            if str(step(diff, poly, 1, 1)) == "break":
                break

def step(diff, poly, start_x=1,lim=1):
    n = "~"
    neg = False
    while re.match("-?\d+$", n) is None:
        n = input(": ")
        if n.lower() in ('q', 'quit'): return "break"
    n = int(n)
    if n < 0:
        neg = True
        n = abs(n)
    if n < start_x or (not neg and poly[n] == 0):
        return
    if poly[n] < 0:
        neg = not neg
    while len(poly) < n + len(diff):
        poly.append(0)
    if neg:
        for i in range(len(diff)):
            poly[n + i - start_x] -= diff[i]
    elif not neg:
        for i in range(len(diff)):
            poly[n + i - start_x] += diff[i]

main()
