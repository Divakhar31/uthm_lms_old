#!/usr/bin/env bash
# Exit immediately if a command exits with a non-zero status
set -o errexit

# 1. Install your standard Python libraries
pip install -r requirements.txt

# 2. Download the STATIC generic Linux version of wkhtmltopdf
echo "Downloading static wkhtmltopdf..."
wget https://github.com/wkhtmltopdf/wkhtmltopdf/releases/download/0.12.4/wkhtmltox-0.12.4_linux-generic-amd64.tar.xz

# 3. Extract it (This creates a folder named 'wkhtmltox')
tar vxf wkhtmltox-0.12.4_linux-generic-amd64.tar.xz

echo "Custom Build complete!"
