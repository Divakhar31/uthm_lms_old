import mysql.connector, os, docx2txt, PyPDF2

# Connect to your DB
db = mysql.connector.connect(host="localhost", user="root", password="", database="uthm_lms", port=3307)
cursor = db.cursor(dictionary=True)

cursor.execute("SELECT submission_id, file_name FROM submissions WHERE extracted_text IS NULL")
rows = cursor.fetchall()

for row in rows:
    path = os.path.join("uploads/submissions", row['file_name'])
    text = ""
    if os.path.exists(path):
        try:
            if path.endswith('.docx'): text = docx2txt.process(path)
            elif path.endswith('.pdf'):
                with open(path, 'rb') as f:
                    pdf = PyPDF2.PdfReader(f)
                    text = " ".join([p.extract_text() for p in pdf.pages if p.extract_text()])
            
            # Update the NULL value with the extracted text
            cursor.execute("UPDATE submissions SET extracted_text = %s WHERE submission_id = %s", (text, row['submission_id']))
            print(f"Fixed ID {row['submission_id']}")
        except Exception as e: print(f"Error on {row['file_name']}: {e}")

db.commit()
print("Done!")