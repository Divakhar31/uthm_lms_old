import mysql.connector
import os

# ====================== DB CONNECTION ======================
def get_db():
    return mysql.connector.connect(
        host=os.environ.get('DB_HOST', 'localhost'),
        user=os.environ.get('DB_USER', 'root'),
        password=os.environ.get('DB_PASSWORD', ''),
        database=os.environ.get('DB_NAME', 'uthm_lms'),
        port=int(os.environ.get('DB_PORT', 3307))
    )
