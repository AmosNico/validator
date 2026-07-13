import json
from collections import defaultdict

GROUP_IDS = ["01", "31", "61"]

def map_id(id_map, parts) :
    parts[1] = id_map[parts[0]][parts[1]]
    todo = {
        "a" : {"b" : [], "u" : [(3, "a"), (4, "a")], "a" : []},
        "e" : {
            "c" : [], "b" : [], "h" : [], "e" : [],
            "n" : [(3, "e")],
            "i" : [(3, "e"), (4, "e")],
            "u" : [(3, "e"), (4, "e")],
            "p" : [(3, "e"), (4, "a")],
            "r" : [(3, "e"), (4, "a")],
        },
        "k" : {
            "d" : [(3, "e"), (5,"k"), (6, "k"), (7, "k")],
            "u" : [(4, "k")],
            "s" : [(6, "k"), (7, "k")]
            # other parts of "s" manually
        }
    }
    q = todo[parts[0]][parts[2]]
    if parts[0] == "k" and parts[2] == "s" :
        if parts[5] in ["ura", "ula", "sua", "sta", "b5"] :
            q += [(3, "a"), (4, "a")]
        else :
            q += [(3, "e"), (4, "e")]
    for (i, T) in q :
        if i < len(parts):
            parts[i] = id_map[T][parts[i]]
    return " ".join(parts)
    

def parse_certificate_tests(filename):
    tests = defaultdict(list)
    universal_lines = []
    group_lines = []
    universal_counter = defaultdict(int)
    group_counter = defaultdict(int)
    test_counter = defaultdict(int)
    current_test = None
    id_map = defaultdict(lambda:dict())
    with open(filename, 'r') as f:
        for line_num, line in enumerate(f, 1):
            stripped = line.strip()
            
            # Skip empty lines and comments
            if not stripped or stripped.startswith('#'):
                continue
            
            # Get the identifier of the line
            parts = stripped.split()
            T = parts[0] # type of statement
            id = parts[1]

            if len(id) == 1:
                id_map[T][id] = str(universal_counter[T])
                universal_counter[T] += 1
                universal_lines.append({
                    'line_number': line_num,
                    'content': stripped,
                    'new_content' : map_id(id_map, parts)
                })
            elif len(id) == 3:
                test_case = id[0:2]
                if current_test != test_case :
                    if test_case in GROUP_IDS :
                        group_lines = []
                        group_counter = defaultdict(int)
                    else :
                        test_counter = defaultdict(int)
                        tests[test_case] = universal_lines + group_lines
                    current_test = test_case
                
                id_map[T][id] = str(universal_counter[T] + group_counter[T] + test_counter[T])
                if test_case in GROUP_IDS :
                    group_lines.append({
                        'line_number': line_num,
                        'content': stripped,
                        'new_content' : map_id(id_map, parts)
                    })
                    group_counter[T] += 1
                else :
                    tests[test_case].append({
                        'line_number': line_num,
                        'content': stripped,
                        'new_content' : map_id(id_map, parts)
                    })
                    test_counter[T] += 1
            else:
                print("Unexpected id")
    return tests

def print_summary(test_data):
    """Print a summary of the parsed test data."""
    print("=" * 60)
    print("TEST CASE SUMMARY")
    print("=" * 60)
    
    total_lines = 0
    for test_case in sorted(test_data.keys()):
        line_count = len(test_data[test_case])
        print(f"\nTestcase {test_case}: {line_count} line(s)")
        total_lines += line_count
    
    print(f"\n{'='*60}")
    print(f"TOTAL: {total_lines} lines across {len(test_data)} testcases")
    print(f"{'='*60}\n")

def save_to_json(test_data, output_file):
    """Save parsed data to JSON file."""
    # Convert defaultdict to regular dict for JSON serialization
    serializable = dict(test_data)
    
    with open(output_file, 'w') as f:
        json.dump(serializable, f, indent=2)
    
    print(f"Saved to {output_file}")

def dump_tests(test_data, dir):
    for test_case in sorted(test_data.keys()):
        data = test_data[test_case]
        file = f"{dir}/{test_case}.txt"
        with open(file, 'w') as f:
            for line in data:
                f.write(line["new_content"] + "\n")



# Main execution
if __name__ == "__main__":
    input_file = "certificate.txt"
    output_file = "certificate_tests_parsed.json"
    out_tests = "certificate"
    
    print(f"Parsing {input_file}...")
    test_data = parse_certificate_tests(input_file)
    
    print("\nParsing complete!")
    print_summary(test_data)
    
    save_to_json(test_data, output_file)

    dump_tests(test_data, out_tests)