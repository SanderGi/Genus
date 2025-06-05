import sys
from parse_tikz import parse_tikz_graph
from collections import defaultdict
import networkx as nx
import matplotlib.pyplot as plt


def plot_parsed_graph(parsed_data):
    """
    Plots the parsed graph data using NetworkX and Matplotlib.

    Args:
        parsed_data: The dictionary returned by parse_tikz_graph.
    """
    if not parsed_data:
        print("No data to plot.")
        return

    G = nx.Graph()
    pos = {}
    node_colors = {}
    node_types = {}
    node_labels = {}
    original_nodes = []
    boundary_nodes = []
    boundary_nodes_for = []

    # Add nodes and prepare plotting data
    for node_id, data in parsed_data["nodes"].items():
        G.add_node(node_id)
        pos[node_id] = (data["x"], data["y"])
        if data["type"] == "original":
            node_types[node_id] = "original"
            node_labels[node_id] = data["label"]
            node_colors[node_id] = "skyblue"
            original_nodes.append(node_id)
        elif data["type"] == "boundary":
            if "for" in data:
                node_types[node_id] = "boundary_for"
                node_labels[node_id] = data["for"]
                node_colors[node_id] = "white"
                boundary_nodes_for.append(node_id)
            else:
                node_types[node_id] = "boundary"
                node_labels[node_id] = data["label"]
                node_colors[node_id] = "lightcoral"
                boundary_nodes.append(node_id)
        else:
            node_colors[node_id] = "grey"  # Should not happen with filtering

    # Add original edges
    original_edges = []
    for edge in parsed_data["edges"]:
        u, v = edge["u"], edge["v"]
        if G.has_node(u) and G.has_node(v):
            G.add_edge(u, v, type="original", color="black")
            original_edges.append((u, v))
        else:
            print(
                f"Warning: Skipping original edge ({u},{v}) - one or both nodes not found."
            )

    # Add boundary edges and group by color
    boundary_edges_by_color = defaultdict(list)
    for pair in parsed_data["boundary_pairs"]:
        color = pair["id"]
        seg1 = pair["segment1"]
        seg2 = pair["segment2"]
        # Add both segments as edges, tagged with color
        if G.has_node(seg1["u"]) and G.has_node(seg1["v"]):
            G.add_edge(seg1["u"], seg1["v"], type="boundary", color=color)
            boundary_edges_by_color[color].append((seg1["u"], seg1["v"]))
        else:
            print(
                f"Warning: Skipping boundary edge ({seg1['u']},{seg1['v']}) for color {color} - nodes not found."
            )

        if G.has_node(seg2["u"]) and G.has_node(seg2["v"]):
            G.add_edge(seg2["u"], seg2["v"], type="boundary", color=color)
            boundary_edges_by_color[color].append((seg2["u"], seg2["v"]))
        else:
            print(
                f"Warning: Skipping boundary edge ({seg2['u']},{seg2['v']}) for color {color} - nodes not found."
            )

    # --- Plotting ---
    plt.figure(figsize=(12, 12))

    # Draw original nodes
    nx.draw_networkx_nodes(
        G,
        pos,
        nodelist=original_nodes,
        node_color="skyblue",
        node_size=300,
        label="Original Nodes",
    )
    # Draw boundary nodes
    nx.draw_networkx_nodes(
        G,
        pos,
        nodelist=boundary_nodes,
        node_color="lightcoral",
        node_size=400,
        node_shape="s",
        label="Boundary Nodes",
    )
    # Draw boundary nodes representing an edge crossing through the boundary
    nx.draw_networkx_nodes(
        G,
        pos,
        nodelist=boundary_nodes_for,
        node_color="white",
        edgecolors="black",
        node_size=400,
        label="Boundary Cross Through Nodes",
    )

    # Draw original edges
    nx.draw_networkx_edges(
        G,
        pos,
        edgelist=original_edges,
        edge_color="black",
        width=1.0,
        label="Original Edges",
    )

    # Draw boundary edges with colors
    # Define a mapping from color names to matplotlib colors if needed
    color_map = {
        "red": "red",
        "blue": "blue",
        "green": "green",
        "orange": "orange",
        "olive": "olive",
        "gray": "gray",
        "pink": "pink",
        "yellow": "yellow",
        "lime": "lime",
        "cyan": "cyan",
        # Add more colors if used by the C code
    }
    for color, edges_list in boundary_edges_by_color.items():
        nx.draw_networkx_edges(
            G,
            pos,
            edgelist=edges_list,
            edge_color=color_map.get(
                color, "purple"
            ),  # Default to purple if color unknown
            width=2.5,  # Make boundary edges thicker
            style="dashed",  # Use dashed style
            label=f"Boundary ({color})",
        )

    # Draw labels
    nx.draw_networkx_labels(G, pos, labels=node_labels, font_size=8)

    plt.title("Parsed Graph Visualization")
    plt.xlabel("X Coordinate")
    plt.ylabel("Y Coordinate")
    # plt.legend() # Legend can get crowded, optional
    plt.axis("equal")  # Ensure aspect ratio is equal
    plt.grid(True)
    plt.show()


# --- Main Execution ---
if __name__ == "__main__":
    tikz = sys.stdin.read()
    parsed_data = parse_tikz_graph(tikz)

    if parsed_data:
        print("\n--- Plotting Parsed Graph ---")
        plot_parsed_graph(parsed_data)
    else:
        print("\nParsing Failed, cannot plot.")
