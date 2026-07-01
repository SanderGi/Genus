from sage.all import var, cos, sin, pi, parametric_plot, parametric_plot3d, point3d  # type: ignore

# ===================== INPUT =====================
# fmt: off
# Graph 1
vertices = [
    ((pi / 2, pi / 4), "blue"), # ((u, v), color)
    ((0, pi / 3), "blue"), 
    ((0, pi / 6), "blue")
]
edges = [
    (0, 1, False, False, "blue"), # (start vertex, end vertex, wrap around, go around)
    (1, 2, False, False, "blue"),
    (2, 0, False, False, "blue"),
]

# Graph 2
# vertices = [
#     ((2 * pi / 3, pi / 6), "blue"), # ((u, v), color)
#     ((4 * pi / 3, pi / 6), "blue"),
#     ((6 * pi / 3, pi / 6), "blue")
# ]
# edges = [
#     (0, 1, False, False, "blue"), # (start vertex, end vertex, wrap around, go around)
#     (1, 2, False, False, "blue"),
#     (2, 0, True, False, "blue"),
# ]

# Graph 3
# vertices = [
#     ((pi / 2, pi / 6), "blue"), # ((u, v), color)
#     ((pi / 2, pi / 2), "blue"),
#     ((pi / 2, 5 * pi / 6), "blue")
# ]
# edges = [
#     (0, 1, False, False, "blue"), # (start vertex, end vertex, wrap around, go around)
#     (1, 2, False, False, "blue"),
#     (2, 0, False, True, "blue"),
# ]
# fmt: on
# =================================================

# Parametric equations for a torus; the fundamental domain is the square [0,2*pi] x [0,2*pi]
var("u v t")
a, b = 2, 1
x = (a + b * cos(u)) * cos(v)
y = (a + b * cos(u)) * sin(v)
z = b * sin(u)


# Function to convert (u, v) to 3D coordinates on the torus
def torus_coords(uh, vh):
    return ((a + b * cos(uh)) * cos(vh), (a + b * cos(uh)) * sin(vh), b * sin(uh))


# Define a function to plot edges along the torus surface by interpolating the (u, v) coordinates
# Optionally wrap around the outside of the torus by modifying the v-coordinate
def edge_on_torus(p1, p2, wrap_around=False, go_around=False, color="blue"):
    uh1, vh1 = p1
    uh2, vh2 = p2

    # Offset the coordinates to wrap around the outside of the torus if wrap_around is True
    if wrap_around:
        uh1 += pi
        uh2 += pi

    # Define the interpolation for the parametric coordinates (u, v)
    u_interp = (1 - t) * uh1 + t * uh2
    v_interp = (1 - t) * vh1 + t * vh2
    if wrap_around:
        u_interp = (1 - t) * uh2 + t * uh1
    if go_around:
        v_interp = (2 - 2 * t) * vh2 + 2 * t * vh1 + 1 * pi / 2

    # Convert the interpolated (u, v) back to 3D space using the torus parametric equations
    x_interp = (a + b * cos(u_interp)) * cos(v_interp)
    y_interp = (a + b * cos(u_interp)) * sin(v_interp)
    z_interp = b * sin(u_interp)

    # Plot the edge as a parametric curve along the surface of the torus
    edge_curve = parametric_plot(
        [x_interp, y_interp, z_interp], (t, 0, 1), color=color, thickness=2
    )
    return edge_curve


# Parametrize the positions of the houses and utilities on the torus
vertex_pos = [(torus_coords(uh, vh), color) for (uh, vh), color in vertices]

# Plot all edges of K(3,3), alternating between inside and outside paths
edge_pos = []
for i, j, wrap_around, go_around, color in edges:
    h = vertices[i][0]
    r = vertices[j][0]
    edge_pos.append(
        edge_on_torus(h, r, wrap_around=wrap_around, go_around=go_around, color=color)
    )

# Combine the plot of the torus and the edges
curve_edges = sum(edge_pos)

# Add points at the vertices
points = []
for pos, color in vertex_pos:
    points.append(point3d(pos, size=10, color=color))

# Plot the torus
T = parametric_plot3d(
    [(a + b * cos(u)) * cos(v), (a + b * cos(u)) * sin(v), b * sin(u)],
    (u, 0, 2 * pi),
    (v, 0, 2 * pi),
    opacity=0.6,
    aspect_ratio=1,
)
final_plot = T + curve_edges + sum(points)

# Show the final plot
# final_plot.show(frame=False)
final_plot.save(
    "torus_plot.png",
    frame=False,
    viewer="tachyon",
    shade="medium",
    antialiasing=True,
    figsize=20,
    zoom=1.5,
    camera_position=[2.3, 2.4, 2.2],
)
