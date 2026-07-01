from adj_format import from_upper_tri

G = from_upper_tri("8 1000111000111111111111111111")
G.plot().save("test.png")
