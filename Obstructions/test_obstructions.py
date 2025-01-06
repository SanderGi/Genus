import sys

from adj_format import from_upper_tri
from genus_algos import run_algorithm


def main(args):
    if len(args) != 1:
        print("Usage: sage test_obstructions.py <obstructions_path>")
        print("Example: sage test_obstructions.py myrvold_minor_obs.txt")
        return

    obstructions_path = args[0]

    disconnected_count = 0
    with open(obstructions_path, "r") as f:
        lines = f.readlines()
        for line in lines:
            g = from_upper_tri(line)

            if not g.is_connected():
                print(line)

                p = g.plot()
                p.save_image(f"disconnected{disconnected_count}.png")

                disconnected_count += 1
            else:
                genus = run_algorithm(g)
                assert genus == 2

    print("Num Disconnected", disconnected_count)
    assert disconnected_count == 3


if __name__ == "__main__":
    main(sys.argv[1:])
