import json
from collections import defaultdict

def parse_certificate_tests(filename):
    # test_data = []
    test_data = defaultdict(lambda: defaultdict(list))
    universal = defaultdict(list)
    counter = {"e" : 0, "k" : 0, "a" : 0}
    idmap = {"e" : defaultdict(int), "k" : defaultdict(int), "a" : defaultdict(int)}
    with open(filename, 'r') as f:
        for line_num, line in enumerate(f, 1):
            stripped = line.strip()
            
            # Skip empty lines and comments
            if not stripped or stripped.startswith('#'):
                continue
            
            # Get the identifier of the line
            parts = stripped.split()
            id = parts[1]
            if len(id) == 1:
                counter[parts[0]] += 1
                universal.append({
                    'line_number': line_num,
                    'identifier': int(id),
                    'content': stripped
                })
            elif len(id) == 3:
                group = int(id[0])  # First digit
                test_case = int(id[1])
                counter[parts[0]] += 1
                
                new_id = int(id[2]) + counter[parts[0]]
                parts[1] = str(new_id)
                test_data[group][test_case].append({
                    'line_number': line_num,
                    'identifier': new_id,
                    'content': stripped,
                    'new_content' : " ".join(parts)
                })
            else:
                print("Unexpected id")
    print(counter)
    return universal, test_data

def print_summary(test_data):
    """Print a summary of the parsed test data."""
    print("=" * 60)
    print("TEST CASE SUMMARY")
    print("=" * 60)
    
    total_lines = 0
    for group in sorted(test_data.keys()):
        print(f"\nGroup {group}:")
        test_cases = test_data[group]
        print(f"  Number of test cases: {len(test_cases)}")
        
        case_line_count = 0
        for test_id in sorted(test_cases.keys()):
            line_count = len(test_cases[test_id])
            case_line_count += line_count
            print(f"    Test {test_id:03d}: {line_count} line(s)")
        
        print(f"  Total lines in group: {case_line_count}")
        total_lines += case_line_count
    
    print(f"\n{'='*60}")
    print(f"TOTAL: {total_lines} lines across {len(test_data)} groups")
    print(f"{'='*60}\n")

def save_to_json(universal, test_data, output_file):
    """Save parsed data to JSON file."""
    # Convert defaultdict to regular dict for JSON serialization
    serializable = { "universal" : universal}
    for group in sorted(test_data.keys()):
        serializable[str(group)] = {}
        for test_case in sorted(test_data[group].keys()):
            serializable[str(group)][str(test_case)] = test_data[group][test_case]
    
    with open(output_file, 'w') as f:
        json.dump(serializable, f, indent=2)
    
    print(f"Saved to {output_file}")

def dump_tests(universal, test_data, dir):
    for group in sorted(test_data.keys()):
        for test_case in sorted(test_data[group].keys()):
            data = test_data[group][test_case]
            file = "{}/{}{}.txt".format(dir, group, test_case)
            with open(file, 'w') as f:
                for line in universal:
                    f.write(line["content"] + "\n")
                for line in data:
                    f.write(line["new_content"] + "\n")



# Main execution
if __name__ == "__main__":
    input_file = "certificate.txt"
    output_file = "certificate_tests_parsed.json"
    out_tests = "certificate"
    
    print(f"Parsing {input_file}...")
    universal, test_data = parse_certificate_tests(input_file)
    
    print("\nParsing complete!")
    print_summary(test_data)
    
    save_to_json(universal, test_data, output_file)

    dump_tests(universal, test_data, out_tests)