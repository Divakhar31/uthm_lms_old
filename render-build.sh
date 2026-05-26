#!/usr/bin/env bash
# Exit immediately if a command exits with a non-zero status
set -o errexit

# 1. Install your standard Python libraries
pip install -r requirements.txt

# 2. Download the Linux version of wkhtmltopdf
echo "Downloading wkhtmltopdf for Linux..."
wget https://github.com/wkhtmltopdf/packaging/releases/download/0.12.6-1/wkhtmltox_0.12.6-1.focal_amd64.deb

# 3. Extract it directly into your project folder so app.py can find it!
dpkg -x wkhtmltox_0.12.6-1.focal_amd64.deb wkhtmltopdf_folder
chmod +x wkhtmltopdf_folder/usr/local/bin/wkhtmltopdf

echo "Custom Build complete!"
