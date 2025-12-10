import os
import graphviz

BASE = "https://github.com/AmosNico/Master-Thesis/tree/main/verifier/"
TARGET_DIRECTORY = "Validator"  # Set the target directory where Lean files are located

LEAN_FILES = [("Validator.lean", "Validator")]

# Collect all Lean files from the target directory and subdirectories
for root, dirs, files in os.walk(TARGET_DIRECTORY):
    for file in files:
        if file.endswith(".lean"):
            path = os.path.join(root, file)
            LEAN_FILES.append((path, path.replace("/", "_")[len(TARGET_DIRECTORY)+1:-5]))

# Create a Graphviz Digraph object
dot = graphviz.Digraph(comment='Lean Files Dependencies')

# Add nodes to the graph
for (file, name) in LEAN_FILES:
    with open(file, "r") as f:
        content = f.read()
        label = name.replace("_", ".")
        basename = os.path.basename(file)[:-5]
        if "sorry" in content:
            dot.node(name, label=f"{label}?", color="red", href=f"{BASE}{basename}.html")
        else:
            dot.node(name, label=f"{label}✓", color="green", href=f"{BASE}{basename}.html")

# Find import dependencies and add edges to the graph
for (file, name) in LEAN_FILES:
    with open(file, "r") as f:
        lines = f.readlines()
        for line in lines:
            if "import Validator." in line:
                imported_module = line.split("import Validator.")[1].strip()
                imported_file = imported_module.replace(".", "_")
                dot.edge(imported_file, name)

# Render the graph to SVG and PNG formats
dot.render('dependencies', format='svg')
dot.render('dependencies', format='png')
