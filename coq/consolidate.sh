#!/bin/bash
# This script combines all .v files into one file with each file's content
# wrapped in triple backticks (```).

# Set the output file name
OUTPUT_FILE="combined.txt"

# Enable nullglob so that the pattern *.v expands to an empty list if no files found
shopt -s nullglob
v_files=( *.v )

# Check if any .v files were found
if [ ${#v_files[@]} -eq 0 ]; then
  echo "No .v files found in the current directory."
  exit 1
fi

# Empty (or create) the output file
> "$OUTPUT_FILE"

# Loop over each .v file
for file in "${v_files[@]}"; do
  echo '```' >> "$OUTPUT_FILE"      # Start code block
  cat "$file" >> "$OUTPUT_FILE"      # Append file contents
  echo '```' >> "$OUTPUT_FILE"      # End code block
  echo "" >> "$OUTPUT_FILE"         # Optional: add an empty line between code blocks
done

echo "Combined code blocks saved to $OUTPUT_FILE"
