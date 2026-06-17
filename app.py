from flask import Flask, render_template, request, redirect, session,flash,send_from_directory, url_for, jsonify, send_file, make_response
import mysql.connector
import smtplib, ssl, random
import os
import datetime
from werkzeug.utils import secure_filename
from werkzeug.security import check_password_hash as werkzeug_check
from werkzeug.security import generate_password_hash
from datetime import datetime
from local_blockchain import Blockchain
from functools import wraps
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics.pairwise import cosine_similarity
from itsdangerous import URLSafeTimedSerializer, SignatureExpired, BadSignature
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
import docx2txt 
import PyPDF2   
import random
import difflib
import io
import concurrent.futures
import re
import pdfkit
import platform
import pyotp
import urllib.parse 
import threading
import uuid
from flask_bcrypt import Bcrypt

def compare_dates_safely(blockchain_date_str, db_date_raw):
    try:
        bc_dt = datetime.strptime(blockchain_date_str, '%Y-%m-%dT%H:%M')
        
        if isinstance(db_date_raw, str):
            db_dt = datetime.strptime(db_date_raw, '%Y-%m-%d %H:%M:%S')
        else:
            db_dt = db_date_raw 

        if bc_dt.replace(second=0, microsecond=0) != db_dt.replace(second=0, microsecond=0):
            return True # REAL TAMPER DETECTED
        else:
            return False # SAFE: Times match exactly

    except Exception as e:
        print(f"Date parsing error: {e}")
        return True

def is_strong_password(password):
    """Checks if a password meets strict security criteria."""
    if len(password) < 8: return False
    if not re.search(r"[A-Z]", password): return False
    if not re.search(r"[a-z]", password): return False
    if not re.search(r"\d", password): return False
    if not re.search(r"[!@#$%^&*(),.?\":{}|<>]", password): return False
    return True

# 1. ADD THIS: The junk filter tells Python to ignore spaces, tabs, and newlines
def is_junk(x):
    return x in " \t\n\r"

def calculate_unified_similarity(text1, text2):
    if not text1 or not text2:
        return 0.0, []

    # ==========================================
    # STEP 1: BLAZING FAST TF-IDF MATH
    # ==========================================
    try:
        # This takes milliseconds and checks for vocabulary overlap
        vectorizer = TfidfVectorizer(stop_words='english')
        tfidf_matrix = vectorizer.fit_transform([text1, text2])
        cosine_sim = cosine_similarity(tfidf_matrix[0:1], tfidf_matrix[1:2])[0][0]
        
        # We square the cosine similarity to punish accidental overlap 
        # and heavily reward actual copy-pasting
        tfidf_score = (cosine_sim ** 2) * 100 
    except Exception:
        tfidf_score = 0.0

    total_matching_chars = 0
    significant_matches = []
    
    # ==========================================
    # STEP 2: EXACT MATCH HIGHLIGHTING (The Heavy Lifter)
    # ==========================================
    # Only run the heavy text-highlighter if the documents actually share vocabulary!
    if tfidf_score > 1.0:
        import re 
        matcher = difflib.SequenceMatcher(is_junk, text1, text2) 
        
        for match in matcher.get_matching_blocks():
            if match.size > 20: 
                # Extract the actual text that was matched
                matched_text = text1[match.a : match.a + match.size]
                
                # SANITY CHECK: Does this match actually contain letters or numbers?
                if not matched_text.strip():
                    continue
                    
                # Strict check: Must contain at least one alphanumeric character
                if not re.search(r'[a-zA-Z0-9]', matched_text):
                    continue

                # If it passes the checks, add it to the score!
                total_matching_chars += match.size
                significant_matches.append(match)

    # Calculate exact match percentage
    avg_length = (len(text1) + len(text2)) / 2
    exact_score = (total_matching_chars / avg_length) * 100 if avg_length > 0 else 0.0

    # ==========================================
    # STEP 3: THE UNIFIED SCORE
    # ==========================================
    # Blend exact sequence matching (80%) with TF-IDF concept matching (20%)
    final_score = round((exact_score * 0.8) + (tfidf_score * 0.2), 1)
    
    return min(final_score, 100.0), significant_matches

app = Flask(__name__)
bcrypt = Bcrypt(app)
app.secret_key = "uthm_secret_2025"
s = URLSafeTimedSerializer(app.secret_key)

UPLOAD_FOLDER = "uploads/submissions"
if not os.path.exists(UPLOAD_FOLDER):
    os.makedirs(UPLOAD_FOLDER)
app.config["UPLOAD_FOLDER"] = UPLOAD_FOLDER

TASK_UPLOAD_FOLDER = "uploads/task_files"
if not os.path.exists(TASK_UPLOAD_FOLDER):
    os.makedirs(TASK_UPLOAD_FOLDER)
app.config["TASK_UPLOAD_FOLDER"] = TASK_UPLOAD_FOLDER

PLAGIARISM_TASKS = {}

def lecturer_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        # THE FIX: Check for the new 'username' and 'role' variables
        if 'username' not in session or session.get('role') != 'lecturer':
            flash('Unauthorized access. Please log in as a lecturer.', 'danger')
            return redirect('/login')
        return f(*args, **kwargs)
    return decorated_function

@app.template_filter('timestamp_to_datetime')
def filter_timestamp_to_datetime(timestamp):
    from datetime import datetime
    try:
        return datetime.fromtimestamp(timestamp).strftime('%Y-%m-%d %H:%M:%S')
    except (TypeError, ValueError):
        return ""

@app.template_filter('hash_block')
def filter_hash_block(block):
    import json
    import hashlib
    block_string = json.dumps(block, sort_keys=True).encode()
    return hashlib.sha256(block_string).hexdigest()

# =================================================================
# UNIVERSAL SECURITY ENGINE (Upgraded with Targeted Alarms & Due Dates!)
# =================================================================
def check_activity_tampering(activity_id, check_scores=True, check_title=True, check_files=True, check_due_date=False):
    try:
        import re
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)
        
        # 1. Fetch current DB Scores & Files
        cursor.execute("SELECT submission_id, plagiarism_score, file_name FROM submissions WHERE activity_id = %s", (activity_id,))
        db_submissions = cursor.fetchall()
        db_scores = {sub['submission_id']: sub['plagiarism_score'] for sub in db_submissions if sub['plagiarism_score'] is not None}
        db_files = set(sub['file_name'] for sub in db_submissions if sub['file_name']) 
        
        # 2. Fetch current DB Activity Details (Added due_date here)
        cursor.execute("SELECT title, due_date FROM activities WHERE id = %s", (activity_id,))
        db_activity = cursor.fetchone()

        cursor.close()
        db_conn.close()

        # 3. Read the Immutable Blockchain Ledger
        activity_chain = Blockchain(identifier=activity_id)
        latest_chain_scores = {}
        latest_chain_title = None
        latest_chain_due_date = None # <--- NEW
        chain_active_files = set() 

        for block in activity_chain.chain:
            for log in block.get('logs', []):
                
                if log['event_type'] == 'SCORE_LOCKED':
                    match = re.search(r"Sub_ID:(\d+)\s*\|\s*Score:([\d\.]+)", log['details'])
                    if match:
                        latest_chain_scores[int(match.group(1))] = float(match.group(2))
                
                elif log['event_type'] in ['ACTIVITY_CREATED', 'ACTIVITY_EDITED']:
                    # Extract Title
                    match_title = re.search(r"Title:\s*(.+?)(?:\s*\||$)", log['details'])
                    if match_title:
                        latest_chain_title = match_title.group(1).strip()
                    
                    # Extract Due Date (e.g., "Title: Lab 1 | DueDate: 2026-12-31 23:59:00")
                    if "DueDate:" in log['details']:
                        try:
                            latest_chain_due_date = log['details'].split("DueDate:")[1].strip()
                        except IndexError:
                            pass
                        
                elif log['event_type'] == 'FILE_UPLOAD':
                    match = re.search(r"Student uploaded file:\s*(.+)", log['details'])
                    if match:
                        chain_active_files.add(match.group(1).strip())
                        
                elif log['event_type'] == 'FILE_DELETE':
                    match = re.search(r"Deleted file:\s*(.+)", log['details'])
                    if match:
                        filename_to_remove = match.group(1).strip()
                        if filename_to_remove in chain_active_files:
                            chain_active_files.remove(filename_to_remove)

        # 4. CROSS-CHECK DATA (Targeted by Parameters)
        
        # Test A: Scores
        if check_scores:
            for sub_id, chain_score in latest_chain_scores.items():
                db_score = db_scores.get(sub_id)
                if db_score is not None and abs(chain_score - float(db_score)) > 0.01:
                    return True 
        
        # Test B: Activity Details (Title)
        if check_title:
            if latest_chain_title and db_activity:
                if latest_chain_title != db_activity['title']:
                    return True 
                
        # Test C: Files
        if check_files:
            if db_files != chain_active_files:
                return True 
                
        # Test D: Due Date (NEW)
        if check_due_date:
            if latest_chain_due_date and db_activity and db_activity.get('due_date'):
                # Use the new safe function instead of strict string comparison
                if compare_dates_safely(latest_chain_due_date, db_activity['due_date']):
                    return True

        return False
        
    except Exception as e:
        print(f"Global Tamper Check Error for Activity {activity_id}: {e}")
        return False
    
# =================================================================
# HELPER: Get exact number of tamper alerts for an activity
# =================================================================
def get_tamper_alert_count(activity_id):
    """Runs a silent audit and returns the total number of tamper alerts."""
    try:
        import re
        activity_chain = Blockchain(identifier=activity_id)
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)
        
        cursor.execute("SELECT title, due_date FROM activities WHERE id = %s", (activity_id,))
        activity = cursor.fetchone()

        cursor.execute("SELECT submission_id, plagiarism_score, file_name FROM submissions WHERE activity_id = %s", (activity_id,))
        db_submissions = cursor.fetchall()
        db_scores = {row['submission_id']: row['plagiarism_score'] for row in db_submissions if row['plagiarism_score'] is not None}
        db_files = set(row['file_name'] for row in db_submissions if row['file_name'])

        latest_chain_scores = {}
        latest_chain_title = None 
        latest_chain_due_date = None
        chain_active_files = set()

        for block in activity_chain.chain:
            for log in block.get('logs', []):
                if log['event_type'] == 'SCORE_LOCKED':
                    match = re.search(r"Sub_ID:(\d+)\s*\|\s*Score:([\d\.]+)", log['details'])
                    if match: latest_chain_scores[int(match.group(1))] = float(match.group(2))
                elif log['event_type'] in ['ACTIVITY_CREATED', 'ACTIVITY_EDITED']:
                    match = re.search(r"Title:\s*(.+?)(?:\s*\||,\s*Type:|$)", log['details'])
                    if match: latest_chain_title = match.group(1).strip()
                    if "DueDate:" in log['details']:
                        try: latest_chain_due_date = log['details'].split("DueDate:")[1].strip()
                        except IndexError: pass
                elif log['event_type'] == 'FILE_UPLOAD':
                    match = re.search(r"Student uploaded file:\s*(.+)", log['details'])
                    if match: chain_active_files.add(match.group(1).strip())
                elif log['event_type'] == 'FILE_DELETE':
                    match = re.search(r"Deleted file:\s*(.+)", log['details'])
                    if match:
                        filename = match.group(1).strip()
                        if filename in chain_active_files: chain_active_files.remove(filename)

        error_count = 0
        
        # Count Score errors
        for sub_id, chain_score in latest_chain_scores.items():
            db_score = db_scores.get(sub_id)
            if db_score is not None and abs(chain_score - float(db_score)) > 0.01: error_count += 1
                
        # Count Title errors
        if latest_chain_title and activity and activity['title'] != latest_chain_title: error_count += 1

        # Count File errors
        for f in db_files:
            if f not in chain_active_files: error_count += 1
        for f in chain_active_files:
            if f not in db_files: error_count += 1

         # Count Due Date errors
        if latest_chain_due_date and activity and activity.get('due_date'):
            # Use the safe function to increment the error count accurately
            if compare_dates_safely(latest_chain_due_date, activity['due_date']):
                error_count += 1

        cursor.close()
        db_conn.close()
        return error_count

    except Exception as e:
        print(f"Error counting alerts for {activity_id}: {e}")
        return 0
    
# ====================== DB CONNECTION ======================
def get_db():
    return mysql.connector.connect(
        host=os.environ.get('DB_HOST', 'localhost'),
        user=os.environ.get('DB_USER', 'root'),
        password=os.environ.get('DB_PASSWORD', ''),
        database=os.environ.get('DB_NAME', 'uthm_lms'),
        port=int(os.environ.get('DB_PORT', 3307))
    )

# ====================== REGISTRATION ======================
@app.route('/register', methods=['GET', 'POST'])
def register():
    if request.method == 'POST':
        fullname = request.form.get('fullname')
        username = request.form.get('username')
        email = request.form.get('email')
        role = request.form.get('role')
        matric_no = request.form.get('matric_no')
        password = request.form.get('password')
        confirm_password = request.form.get('confirm_password')

        # 1. Check if passwords match
        if password != confirm_password:
            flash('Passwords do not match!', 'danger')
            return redirect('/register')

        # 2. Check if password is strong enough
        if not is_strong_password(password):
            flash('Password is too weak. Please meet all the security requirements.', 'danger')
            return redirect('/register')

        db_conn = None
        cursor = None
        try:
            db_conn = get_db()
            cursor = db_conn.cursor(dictionary=True)

            # 3. Check if username or email is already taken
            cursor.execute("SELECT * FROM users WHERE username = %s OR email = %s", (username, email))
            existing_user = cursor.fetchone()
            if existing_user:
                flash('Username or Email is already registered. Please log in or choose another.', 'danger')
                return redirect('/register')

            # 4. Hash the password securely and save to database
            hashed_pw = bcrypt.generate_password_hash(password).decode('utf-8')

            cursor.execute("""
                INSERT INTO users (username, password, email, role, fullname, matric_no) 
                VALUES (%s, %s, %s, %s, %s, %s)
            """, (username, hashed_pw, email, role, fullname, matric_no))
            
            db_conn.commit()

            # Success!
            flash('Registration successful! You can now log in.', 'success')
            return redirect('/login') 

        except Exception as e:
            if db_conn:
                db_conn.rollback()
            print(f"Registration Error: {e}")
            flash('An error occurred during registration. Please try again.', 'danger')
            return redirect('/register')
            
        finally:
            if cursor: cursor.close()
            if db_conn: db_conn.close()

    # GET Request: Show the HTML page
    return render_template('register.html')

# ====================== CHANGE PASSWORD ======================
@app.route('/change-password', methods=['GET', 'POST'])
def change_password():
    if 'username' not in session:
        flash('Please log in to change your password.', 'warning')
        return redirect('/')

    if request.method == 'POST':
        current_password = request.form.get('current_password')
        new_password = request.form.get('new_password')
        confirm_password = request.form.get('confirm_password')

        # 1. Check if the two new passwords match
        if new_password != confirm_password:
            flash('New passwords do not match!', 'danger')
            return redirect('/change-password')

        # 🚨 NEW: Strong Password Validation
        if len(new_password) < 8:
            flash('Password must be at least 8 characters long.', 'danger')
            return redirect('/change-password')
        if not re.search(r"[A-Z]", new_password):
            flash('Password must contain at least one uppercase letter.', 'danger')
            return redirect('/change-password')
        if not re.search(r"[a-z]", new_password):
            flash('Password must contain at least one lowercase letter.', 'danger')
            return redirect('/change-password')
        if not re.search(r"\d", new_password):
            flash('Password must contain at least one number.', 'danger')
            return redirect('/change-password')

        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)
        
        try:
            # 2. Fetch the user's current password
            cursor.execute("SELECT password FROM users WHERE username = %s", (session.get('username'),))
            user = cursor.fetchone()
            
            if not user:
                flash('User not found.', 'danger')
                return redirect('/change-password')

            stored_hash = user['password']
            is_authenticated = False

            # 3. Verify current password (Handle both old scrypt and new bcrypt)
            if stored_hash.startswith('scrypt:'):
                if werkzeug_check(stored_hash, current_password):
                    is_authenticated = True
            else:
                if bcrypt.check_password_hash(stored_hash, current_password):
                    is_authenticated = True

            # If neither check passed, the current password was wrong
            if not is_authenticated:
                flash('Incorrect current password.', 'danger')
                return redirect('/change-password')

            # 4. Hash the NEW password strictly using Bcrypt and update the database
            new_hashed_password = bcrypt.generate_password_hash(new_password).decode('utf-8')
            
            cursor.execute("UPDATE users SET password = %s WHERE username = %s", (new_hashed_password, session.get('username')))
            db_conn.commit()

            flash('Password successfully updated!', 'success')
            return redirect('/change-password')

        except Exception as e:
            db_conn.rollback()
            print(f"Error changing password: {e}")
            flash('An error occurred while updating your password.', 'danger')
        finally:
            cursor.close()
            db_conn.close()

    return render_template('change_password.html')
# ==========================================
# 1. FORGOT PASSWORD (Enter Username)
# ==========================================
@app.route('/forgot_password', methods=['GET', 'POST'])
def forgot_password():
    if request.method == 'POST':
        username = request.form.get('username')
        
        db = get_db()
        cursor = db.cursor(dictionary=True)
        cursor.execute("SELECT * FROM users WHERE username = %s", (username,))
        user = cursor.fetchone()
        cursor.close()
        db.close()
        
        if user and user.get('totp_secret'):
            # If they exist and have 2FA setup, send them to verify it
            session['reset_user'] = username
            return redirect('/verify_reset_2fa')
        elif user and not user.get('totp_secret'):
            flash('2-Step Verification is not enabled for this account. Contact your lecturer to reset your password.', 'danger')
        else:
            # Vague error so hackers can't guess usernames
            flash('If that username exists, please enter your Authenticator code on the next page.', 'info')
            
    return render_template('forgot_password.html')


# ==========================================
# 2. VERIFY 2FA FOR PASSWORD RESET
# ==========================================
@app.route('/verify_reset_2fa', methods=['GET', 'POST'])
def verify_reset_2fa():
    username = session.get('reset_user')
    if not username: 
        return redirect('/forgot_password')

    if request.method == 'POST':
        code = request.form.get('code')
        
        db = get_db()
        cursor = db.cursor(dictionary=True)
        cursor.execute("SELECT totp_secret FROM users WHERE username = %s", (username,))
        user = cursor.fetchone()
        cursor.close()
        db.close()

        totp = pyotp.TOTP(user['totp_secret'])
        
        if totp.verify(code):
            # Code is correct! Grant them access to the reset page
            session['authorized_reset'] = True
            return redirect('/reset_password')
        else:
            flash('Invalid Authenticator code. Please try again.', 'danger')

    return render_template('verify_reset_2fa.html')


# ==========================================
# 3. CREATE NEW PASSWORD
# ==========================================
@app.route('/reset_password', methods=['GET', 'POST'])
def reset_password():
    # Security check: Make sure they successfully passed the 2FA check first!
    if not session.get('authorized_reset') or not session.get('reset_user'):
        return redirect('/')

    if request.method == 'POST':
        new_password = request.form.get('password')
        confirm_password = request.form.get('confirm_password')

        # 1. Check if passwords match
        if new_password != confirm_password:
            flash('Passwords do not match.', 'danger')
            return redirect('/reset_password')

        # 2. Check if the new password is strong enough
        if not is_strong_password(new_password):
            flash('New password is too weak. Please meet all the security requirements.', 'danger')
            return redirect('/reset_password')

        # 3. Hash and save the new password
        hashed_pw = generate_password_hash(new_password)
        username = session.get('reset_user')
        
        db = get_db()
        cursor = db.cursor()
        cursor.execute("UPDATE users SET password = %s WHERE username = %s", (hashed_pw, username))
        db.commit()
        cursor.close()
        db.close()
        
        # 4. Clean up the session variables so they can't reuse this page later
        session.pop('reset_user', None)
        session.pop('authorized_reset', None)
        
        flash('Password reset successful! You can now log in with your new password.', 'success')
        return redirect('/login')

    # GET Request: Show the HTML page
    return render_template('reset_password.html')

# ====================== SEND EMAIL ======================
def send_email(receiver_email, code):
    sender_email = "divakhar.raj31@gmail.com"
    password = "fyvvufjogdgoztlu"
    message = f"Subject: Login Verification Code\n\nYour verification code is {code}"

    context = ssl.create_default_context()
    with smtplib.SMTP_SSL("smtp.gmail.com", 465, context=context) as server:
        server.login(sender_email, password)
        server.sendmail(sender_email, receiver_email, message)

# ====================== SMART HOMEPAGE ROUTER ======================
@app.route('/')
def index():
    # If they are already fully logged in, send them to their dashboard
    if 'username' in session and 'role' in session:
        if session.get('role') == 'lecturer':
            return redirect('/lecturer/dashboard')
        elif session.get('role') == 'student':
            return redirect(f"/student/dashboard/{session.get('username')}")
    
    # Otherwise, force them to log in
    return redirect(url_for('login'))

# ====================== LOGIN ======================
@app.route('/login', methods=['GET', 'POST'])
def login():
    if request.method == 'POST':
        username = request.form.get('username')
        password_attempt = request.form.get('password')

        db_conn = None
        cursor = None
        try:
            db_conn = get_db()
            cursor = db_conn.cursor(dictionary=True)

            # Fetch the user from the database
            cursor.execute("SELECT * FROM users WHERE username = %s", (username,))
            user = cursor.fetchone()

            # Check if the user actually exists
            if user:
                stored_hash = user['password']
                is_authenticated = False

                # 1. Check if this is an OLD user (their hash starts with 'scrypt:')
                if stored_hash.startswith('scrypt:'):
                    if werkzeug_check(stored_hash, password_attempt):
                        # SUCCESS! Upgrade them to Bcrypt behind the scenes
                        new_bcrypt_hash = bcrypt.generate_password_hash(password_attempt).decode('utf-8')
                        cursor.execute("UPDATE users SET password = %s WHERE id = %s", (new_bcrypt_hash, user['id']))
                        db_conn.commit()
                        is_authenticated = True

                # 2. Check if this is a NEW user (Bcrypt)
                else:
                    if bcrypt.check_password_hash(stored_hash, password_attempt):
                        is_authenticated = True

                # 3. If they passed either check above, proceed to 2FA
                if is_authenticated:
                    # Clear any old session data first
                    session.clear() 

                    # Check if this user has already set up their Authenticator App
                    if user.get('totp_secret'):
                        # They HAVE set it up. Send them to verify the 6-digit code.
                        session['pending_user'] = user['username']
                        session['pending_role'] = user.get('role')
                        return redirect('/verify_2fa')
                    else:
                        # They HAVE NOT set it up. Force them to scan the QR code first.
                        session['setup_user'] = user['username']
                        session['setup_role'] = user.get('role')
                        return redirect('/setup_2fa')
                        
                else:
                    # User exists, but the password was wrong
                    flash('Invalid username or password', 'danger')
                    return redirect('/login')

            else:
                # User does not exist at all
                flash('Invalid username or password', 'danger')
                return redirect('/login')

        except Exception as e:
            if db_conn:
                db_conn.rollback()
            print(f"Login Error: {e}")
            flash('An error occurred during login. Please try again.', 'danger')
            return redirect('/login')
            
        finally:
            if cursor: cursor.close()
            if db_conn: db_conn.close()

    # GET Request: Show the HTML page
    return render_template('login.html')

# ==========================================
# SETUP 2FA (QR Code Generation)
# ==========================================
@app.route('/setup_2fa', methods=['GET', 'POST'])
def setup_2fa():
    username = session.get('setup_user')
    if not username: 
        return redirect('/login')

    if request.method == 'POST':
        secret = session.get('new_totp_secret')
        code = request.form.get('code')
        
        # Safety check: If session dropped the secret, don't crash
        if not secret:
            flash('Session expired. Please scan the new QR code.', 'warning')
            return redirect('/setup_2fa')

        totp = pyotp.TOTP(secret)
        
        # valid_window=1 gives a 30s grace period
        if totp.verify(code, valid_window=1):
            db_conn = get_db()
            cursor = db_conn.cursor()
            cursor.execute("UPDATE users SET totp_secret = %s WHERE username = %s", (secret, username))
            db_conn.commit()
            cursor.close()
            db_conn.close()

            # Officially log them in
            session['username'] = username
            session['role'] = session.get('setup_role')
            
            # Clean up temporary session data
            session.pop('setup_user', None)
            session.pop('setup_role', None)
            session.pop('new_totp_secret', None) 
            
            flash('2-Step Verification enabled successfully!', 'success')
            
            # IMPORTANT: Update these to match your actual dashboard routes!
            if session.get('role') == 'lecturer':
                return redirect('/lecturer/dashboard') 
            return redirect(f"/student/dashboard/{session['username']}")
        else:
            flash('Invalid code. Please try again.', 'danger')
            return redirect('/setup_2fa')

    # GET REQUEST: Generate a new secret ONLY if one doesn't exist yet
    if 'new_totp_secret' not in session:
        session['new_totp_secret'] = pyotp.random_base32()
        
    secret = session['new_totp_secret']
    
    totp_uri = pyotp.totp.TOTP(secret).provisioning_uri(name=username, issuer_name="UTHM Portal")
    qr_url = f"https://api.qrserver.com/v1/create-qr-code/?size=200x200&data={urllib.parse.quote(totp_uri)}"

    return render_template('setup_2fa.html', secret=secret, qr_url=qr_url)


# ==========================================
# VERIFY 2FA (Daily Login)
# ==========================================
@app.route('/verify_2fa', methods=['GET', 'POST'])
def verify_2fa():
    username = session.get('pending_user')
    if not username: 
        return redirect('/login')

    if request.method == 'POST':
        code = request.form.get('code')
        
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)
        # Fetch role directly from DB to be extra safe
        cursor.execute("SELECT totp_secret, role FROM users WHERE username = %s", (username,))
        user = cursor.fetchone()
        cursor.close()
        db_conn.close()

        # Crash prevention: Check if user exists and has a secret
        if not user or not user.get('totp_secret'):
            flash('2FA is not set up for this account. Please log in again.', 'danger')
            session.clear()
            return redirect('/login')

        totp = pyotp.TOTP(user['totp_secret'])
        
        # ADDED THE MISSING valid_window=1 HERE!
        if totp.verify(code, valid_window=1):
            
            session['username'] = username
            session['role'] = user.get('role') 
            
            session.pop('pending_user', None)
            session.pop('pending_role', None)
            
            # IMPORTANT: Update these to match your actual dashboard routes!
            if session.get('role') == 'lecturer':
                return redirect('/lecturer/dashboard') 
            return redirect(f"/student/dashboard/{session['username']}")
        else:
            flash('Invalid 6-digit code. Please try again.', 'danger')

    return render_template('verify_2fa.html')

# ====================== VERIFY PAGE ======================
@app.route('/verify', methods=['GET', 'POST'])
def verify():
    if 'username' not in session:
        return redirect(url_for('login'))

    if request.method == 'POST':
        entered_code = request.form.get('code')

        # 1️⃣ OTP expiry (5 minutes)
        if datetime.now().timestamp() - session.get('otp_time', 0) > 300:
            session.clear()
            return redirect(url_for('login'))

        # 2️⃣ OTP matches?
        if str(entered_code) == str(session.get('verification_code')):
            session['logged_in'] = True
            session.pop('verification_code', None)
            session.pop('otp_time', None)

            username = session.get('username')
            role = session.get('role')

            db_conn = get_db()
            cursor = db_conn.cursor(dictionary=True)

            if role == 'lecturer':
                # Fetch lecturer info
                cursor.execute("SELECT id, fullname FROM users WHERE username=%s", (username,))
                lecturer = cursor.fetchone()

                if not lecturer:
                    cursor.close()
                    db_conn.close()
                    session.clear()
                    return "Lecturer not found", 404

                session['user_id'] = lecturer['id']
                session['fullname'] = lecturer['fullname']

                # Get first course ID for lecturer
                lecturer_name_db = lecturer['fullname'].split(' ')[0]  # matches your DB naming
                cursor.execute("""
                    SELECT id AS course_id
                    FROM courses
                    WHERE lecturer=%s
                    ORDER BY id ASC
                    LIMIT 1
                """, (lecturer_name_db,))
                first_course = cursor.fetchone()

                cursor.close()
                db_conn.close()

                if first_course:
                    course_id = first_course['course_id']
                    return redirect(f"/lecturer/dashboard/{course_id}")
                else:
                    return "You are logged in, but you are not assigned to any courses.", 200

            else:  # student
                # Fetch student info
                cursor.execute("SELECT id, fullname, username FROM users WHERE username=%s", (username,))
                student = cursor.fetchone()
                cursor.close()
                db_conn.close()

                if not student:
                    session.clear()
                    return "Student record not found", 404

                session['user_id'] = student['id']
                session['fullname'] = student['fullname']

                # Redirect to student dashboard using student ID
                student_id = student['id']
                return redirect(f"/student/dashboard/{student_id}")

        # 3️⃣ OTP invalid
        return render_template('verify.html', error="Invalid verification code")

    # GET request → show OTP form
    return render_template('verify.html')

# ====================== STUDENT DASHBOARD ======================
@app.route("/student/dashboard/<string:student_username>")
def student_dashboard(student_username):
    # Security check: Make sure they are logged in AND their session matches the URL
    if 'username' not in session or session.get('role') != 'student' or session.get('username') != student_username:
        return redirect('/')

    username = session.get("username")
    db_conn = get_db()
    cur = db_conn.cursor(dictionary=True)

    # 1. THE FIX: Fetch the actual full name directly from the database
    cur.execute("SELECT fullname FROM users WHERE username = %s", (username,))
    user_data = cur.fetchone()
    user_fullname = user_data['fullname'] if user_data else 'Student Name'

    # 2. Fetch classrooms for this student
    cur.execute("""
        SELECT c.id AS course_id, c.course_code, c.course_name
        FROM student_courses sc
        JOIN courses c ON sc.course_id = c.id
        WHERE sc.student_username = %s
    """, (username,)) 
    classrooms = cur.fetchall()
    
    cur.close()
    db_conn.close()

    return render_template(
        "dashboard_student.html",
        classrooms=classrooms,
        user={'fullname': user_fullname} # We pass the real name to the HTML here!
    )

# ====================== STUDENT IND ACTIVITY (FULL SECURITY INTEGRATION) ======================
@app.route('/student/activities/individual/<int:course_id>', methods=['GET'])
def student_view_individual_activities(course_id):
    if 'username' not in session or session.get('role') != 'student':
        return redirect('/')

    db_conn = get_db()
    cursor = db_conn.cursor(dictionary=True) 

    # 1. Get user & course info
    cursor.execute("SELECT fullname FROM users WHERE username = %s", (session.get('username'),))
    user = cursor.fetchone() 
    cursor.execute("SELECT course_code, course_name FROM courses WHERE id = %s", (course_id,))
    course = cursor.fetchone()

    # 2. Get activities 
    cursor.execute("SELECT * FROM activities WHERE course_id = %s AND type = 'individual' ORDER BY due_date ASC", (course_id,))
    activities = cursor.fetchall()
    
    # 3. Categorization & Submission Linking
    categorized_activities = {'Assignments': [], 'Projects': [], 'Labs': [], 'Other': []}
    
    # Security Scan Variable
    any_activity_tampered = False
    
    for act in activities:
        # Relink Database Submissions
        cursor.execute("""
            SELECT submission_id as id, file_name, submitted_on as submitted_at 
            FROM submissions 
            WHERE activity_id = %s AND student_username = %s
        """, (act['id'], session.get('username')))
        
        student_files = cursor.fetchall()
        act['student_files'] = student_files
        act['has_submitted'] = len(student_files) > 0
        act['is_late'] = any(f['submitted_at'] > act['due_date'] for f in student_files)

        # Categorize
        title_lower = act['title'].lower()
        if 'assignment' in title_lower: categorized_activities['Assignments'].append(act)
        elif 'project' in title_lower: categorized_activities['Projects'].append(act)
        elif 'lab' in title_lower: categorized_activities['Labs'].append(act)
        else: categorized_activities['Other'].append(act)

        # --- SECURITY SCAN ---
    any_activity_tampered = False
    tampered_titles = [] # 🚨 NEW: List to hold the names of compromised activities
    
    for act in activities:
        # Relink Database Submissions
        # ... [Your existing submission linking code remains here] ...

        # Categorize
        # ... [Your existing categorization code remains here] ...

        # Run the full-spectrum security scan
        if check_activity_tampering(act['id'], check_scores=True, check_title=True, check_files=True, check_due_date=True):
            any_activity_tampered = True
            tampered_titles.append(act['title']) # 🚨 NEW: Save the title if a hack is detected

    cursor.close()
    db_conn.close()

    return render_template('individual_activity_student.html',
                           user=user,         
                           course=course,     
                           course_id=course_id,
                           activities=activities, 
                           categorized_activities=categorized_activities, 
                           now=datetime.now(),
                           db_tampered=any_activity_tampered,
                           tampered_titles=tampered_titles # 🚨 NEW: Pass the titles to the template
                          )

# ====================== SUBMIT ACTIVITY (FIXED FOR MULTI-FILE) ======================
@app.route('/student/submit_activity', methods=['POST'])
def student_submit_activity(): 
    if 'username' not in session or session.get('role') != 'student':
        return redirect('/')
    
    # Get activity_id from the form data (passed as a hidden field)
    activity_id = request.form.get('activity_id', type=int)
    if activity_id is None:
        flash('Activity ID is missing.', 'danger')
        return redirect(request.referrer or url_for('student_dashboard'))
        
    student_username = session.get('username')
    
    # CRITICAL FIX: Use getlist to handle multiple files from the 'submission_files' input name
    uploaded_files = request.files.getlist('submission_files') 
    
    # Filter out empty entries (e.g., if user opens the dialog but selects nothing)
    uploaded_files = [f for f in uploaded_files if f.filename]

    if not uploaded_files:
        flash('No files selected for uploading.', 'danger')
        return redirect(request.referrer or url_for('student_dashboard'))
    
    db_conn = None
    cursor = None
    course_id = None
    files_processed = [] # To track successfully saved files for clean up/logging
    
    try:
        db_conn = get_db()
        # Use dictionary=True so we can access fetchone results by column name
        cursor = db_conn.cursor(dictionary=True) 

        # 1. Fetch course_id (needed for the DB record and final redirect)
        cursor.execute("SELECT course_id FROM activities WHERE id = %s", (activity_id,))
        result = cursor.fetchone()
        if result is None:
            raise Exception("Activity not found in database.")
        course_id = result['course_id']

        # --- Loop through ALL uploaded files ---
        for file in uploaded_files:
            filename_secure = secure_filename(file.filename)
            timestamp_ms = int(datetime.now().timestamp() * 1000) 
            file_name_db = f"{student_username}_{activity_id}_{timestamp_ms}_{filename_secure}"
            save_path = os.path.join(app.config["UPLOAD_FOLDER"], file_name_db)

            # 1. Save the file to disk
            file.save(save_path)

            # 2. Extract text immediately after saving
            extracted = ""
            try:
                if filename_secure.lower().endswith('.docx'):
                    extracted = docx2txt.process(save_path)
                elif filename_secure.lower().endswith('.pdf'):
                    with open(save_path, 'rb') as f:
                        pdf = PyPDF2.PdfReader(f)
                        extracted = " ".join([p.extract_text() for p in pdf.pages if p.extract_text()])
                else:
                    with open(save_path, 'r', encoding='utf-8', errors='ignore') as f:
                        extracted = f.read()
            except Exception as e:
                print(f"Extraction error: {e}")
                extracted = "Error extracting text content."

            # 3. Database Record
            query = """
            INSERT INTO submissions 
            (student_username, course_id, activity_id, file_name, submitted_on, submitted_at, extracted_text)
            VALUES (%s, %s, %s, %s, CONVERT_TZ(NOW(), '+00:00', '+08:00'), CONVERT_TZ(NOW(), '+00:00', '+08:00'), %s)
            """
            cursor.execute(query, (
                student_username, 
                course_id, 
                activity_id, 
                file_name_db,
                extracted # <--- THIS WAS THE BUG! Changed from extracted_content to extracted
            ))
            
            files_processed.append({'file_name_db': file_name_db, 'save_path': save_path})
        
        db_conn.commit()
        
        flash(f'{len(files_processed)} file(s) successfully uploaded!', 'success')
        
        # --- BLOCKCHAIN INTEGRATION ---
        activity_chain = Blockchain(identifier=activity_id) 
        for f in files_processed:
            activity_chain.new_log(
                sender=session['username'],
                recipient=activity_id, 
                event_type="FILE_UPLOAD", 
                details=f"Student uploaded file: {f['file_name_db']}"
            )

        # Mine block once after all logs are added
        last_proof = activity_chain.last_block['proof']
        proof = activity_chain.proof_of_work(last_proof)
        activity_chain.new_block(proof)
        flash('All file uploads logged to the immutable audit trail!', 'info')

        
    except Exception as e:
        if db_conn:
            db_conn.rollback()
        # If any step fails, try to remove all files that were successfully saved so far
        for f in files_processed:
            if os.path.exists(f['save_path']):
                os.remove(f['save_path'])
        print(f"Database/File Save Error during submission: {e}")
        flash('Error submitting activity. Please try again. Check if activity is still open or database error occurred.', 'danger')
        
    finally:
        if cursor:
            cursor.close()
        if db_conn:
            db_conn.close()

    # Final Return 
    if course_id:
        return redirect(url_for('student_view_individual_activities', course_id=course_id))
    else:
        return redirect('/student/dashboard')
    
# ====================== DELETE SUBMISSION FILE ======================
# Updated route name to match your HTML's expected URL
@app.route('/student/delete_submission_file/<int:file_id>', methods=['POST'])
def student_delete_submission_file(file_id):
    if 'username' not in session:
        return redirect('/')

    db_conn = None
    cursor = None
    course_id = None # INITIALIZED to prevent UnboundLocalError
    
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)
        
        # FIX: Using 'submission_id' from your DESCRIBE output
        cursor.execute("""
            SELECT file_name, activity_id, course_id 
            FROM submissions 
            WHERE submission_id = %s
        """, (file_id,))
        
        file_record = cursor.fetchone()

        if file_record:
            course_id = file_record['course_id']
            
            # Delete from physical folder
            file_path = os.path.join(app.config['UPLOAD_FOLDER'], file_record['file_name'])
            if os.path.exists(file_path):
                os.remove(file_path)

            # Delete from Database using submission_id
            cursor.execute("DELETE FROM submissions WHERE submission_id = %s", (file_id,))
            
            # Blockchain Logging
            activity_chain = Blockchain(identifier=file_record['activity_id'])
            activity_chain.new_log(
                sender=session['username'],
                recipient=file_record['activity_id'],
                event_type="FILE_DELETE",
                details=f"Deleted file: {file_record['file_name']}"
            )
            activity_chain.new_block(activity_chain.proof_of_work(activity_chain.last_block['proof']))
            
            db_conn.commit()
            flash('File deleted successfully.', 'success')
        else:
            flash('Submission record not found.', 'warning')

    except Exception as e:
        if db_conn:
            db_conn.rollback()
        print(f"Delete Error: {e}")
        flash('Error during deletion.', 'danger')
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()
    
    # SAFE REDIRECT: If course_id wasn't found, go to dashboard
    if course_id:
        return redirect(url_for('student_view_individual_activities', course_id=course_id))
    return redirect(url_for('student_dashboard'))

# ====================== LECTURER: MARK ALERT AS READ ======================
@app.route('/lecturer/acknowledge_tamper/<int:activity_id>', methods=['POST'])
@lecturer_required
def acknowledge_tamper(activity_id):
    db_conn = None
    cursor = None
    try:
        # 1. Run the security scan to see how many errors exist RIGHT NOW
        import re
        activity_chain = Blockchain(identifier=activity_id)
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)
        
        # (Quickly count ghost files, score mismatches, etc. using your existing check logic)
        # To keep it simple, we will just use the length of the hacked submissions/files.
        cursor.execute("SELECT submission_id FROM submissions WHERE activity_id = %s", (activity_id,))
        current_db_count = len(cursor.fetchall())
        
        # We use a combined hash or count of the current state. 
        # For this fix, let's just use a placeholder logic that forces a reset if the db rows change, 
        # or you can pass the specific 'alert_count' from the frontend HTML form!
        alert_count = request.form.get('alert_count', 1) 

        # 2. Save the acknowledgment WITH the count
        cursor.execute("""
            INSERT INTO acknowledged_tampers (activity_id, acknowledged_by, alert_count) 
            VALUES (%s, %s, %s)
            ON DUPLICATE KEY UPDATE alert_count = VALUES(alert_count), acknowledged_at = CURRENT_TIMESTAMP
        """, (activity_id, session.get('username'), alert_count))
        db_conn.commit()
        
        flash('Tamper alert acknowledged. It has been hidden from the main dashboard.', 'success')
        return redirect(request.referrer or f'/lecturer/blockchain_audit_activity/{activity_id}')
        
    except Exception as e:
        if db_conn: db_conn.rollback()
        import traceback
        traceback.print_exc()
        flash('Error acknowledging alert.', 'danger')
        return redirect(request.referrer)
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== LECTURER DASHBOARD (FIXED) ======================
@app.route("/lecturer/dashboard/<int:course_id>", methods=['GET'])
def lecturer_dashboard_view(course_id): 
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/')

    lecturer_username_session = session['username'] 

    db_conn = get_db()
    cursor = db_conn.cursor(dictionary=True)

    # 1. Fetch User Details 
    cursor.execute("SELECT fullname FROM users WHERE username=%s", (lecturer_username_session,))
    user = cursor.fetchone()

    # 2. Get lecturer's name for course querying
    lecturer_name_db = user['fullname'].split(' ')[0] 

    # 3. Fetch ALL Classrooms for the radio buttons
    cursor.execute("""
        SELECT id AS course_id, course_code, course_name
        FROM courses
        WHERE lecturer = %s 
    """, (lecturer_name_db,)) 

    classrooms = cursor.fetchall()

    # 4. Fetch Details of the CURRENTLY SELECTED Course (for the page title/header)
    cursor.execute("SELECT course_code, course_name FROM courses WHERE id = %s", (course_id,)) 
    current_course_info = cursor.fetchone()

    cursor.close()
    db_conn.close()

    return render_template("dashboard_lecturer.html", 
                           course_id=course_id, # The ID from the URL is passed
                           user=user, 
                           classrooms=classrooms,
                           current_course=current_course_info # Can be used to display the current course name
                           )

# ====================== STUDENT NAME LIST ======================
@app.route('/lecturer/students/<int:course_id>', methods=['GET'])
@lecturer_required
def view_student_list(course_id):
    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)

        # ---> THE FIX: Fetch the logged-in lecturer's full name for the sidebar <---
        cursor.execute("SELECT fullname FROM users WHERE username = %s", (session.get('username'),))
        current_user = cursor.fetchone()

        # 1. Get Course Info
        cursor.execute("SELECT course_code, course_name FROM courses WHERE id = %s", (course_id,))
        course = cursor.fetchone()

        if not course:
            flash("Course not found.", "danger")
            return redirect('/lecturer/dashboard')

        # 2. Find out how many total activities exist for this course
        cursor.execute("SELECT COUNT(*) as total_acts FROM activities WHERE course_id = %s", (course_id,))
        total_activities = cursor.fetchone()['total_acts']

        # 3. Get Enrolled Students
        query = """
            SELECT u.fullname, u.username, u.email 
            FROM student_courses e
            JOIN users u ON e.student_username = u.username
            WHERE e.course_id = %s
            ORDER BY u.fullname ASC
        """
        cursor.execute(query, (course_id,))
        students = cursor.fetchall()

        # 4. THE RADAR LOGIC: Calculate risk for every student
        high_risk_count = 0
        warning_count = 0

        for student in students:
            sub_query = """
                SELECT COUNT(DISTINCT s.activity_id) as sub_count 
                FROM submissions s 
                JOIN activities a ON s.activity_id = a.id 
                WHERE a.course_id = %s AND s.student_username = %s
            """
            cursor.execute(sub_query, (course_id, student['username']))
            completed = cursor.fetchone()['sub_count']
            
            student['completed_tasks'] = completed
            student['total_tasks'] = total_activities

            # Determine Risk Status based on completion
            if total_activities == 0:
                student['risk_level'] = 'No Data'
            else:
                completion_rate = completed / total_activities
                
                if completion_rate >= 0.80:       
                    student['risk_level'] = 'On Track'
                elif completion_rate >= 0.50:     
                    student['risk_level'] = 'Warning'
                    warning_count += 1
                else:                             
                    student['risk_level'] = 'High Risk'
                    high_risk_count += 1

        # ---> THE FIX: Pass `user=current_user` to the HTML <---
        return render_template('student_list.html', 
                               course=course, 
                               students=students, 
                               course_id=course_id,
                               high_risk=high_risk_count,
                               warning=warning_count,
                               user=current_user)

    except Exception as e:
        import traceback
        traceback.print_exc()
        return f"System Error: {e}", 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== STUDENT AUDIT ======================
@app.route('/lecturer/api/student_audit/<int:course_id>/<username>', methods=['GET'])
@lecturer_required
def get_student_audit(course_id, username):
    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)

        # 1. Get the student's full name
        cursor.execute("SELECT fullname FROM users WHERE username = %s", (username,))
        student = cursor.fetchone()

        # 2. Grab activities and the plagiarism score
        query = """
            SELECT a.id, a.title, a.due_date, 
                   s.submission_id, s.submitted_on, s.plagiarism_score
            FROM activities a
            LEFT JOIN submissions s ON a.id = s.activity_id AND s.student_username = %s
            WHERE a.course_id = %s
            ORDER BY a.due_date ASC
        """
        cursor.execute(query, (username, course_id))
        activities = cursor.fetchall()

        now = datetime.now()
        audit_data = []
        
        for act in activities:
            
            # --- SAFETY NET 1: Bulletproof Dates ---
            due_date = act['due_date']
            if isinstance(due_date, str):
                due_date = datetime.strptime(due_date[:16].replace('T', ' '), '%Y-%m-%d %H:%M')
                
            submitted_on = act['submitted_on']
            submitted_date_text = None
            if submitted_on:
                if isinstance(submitted_on, str):
                    submitted_on = datetime.strptime(submitted_on[:16].replace('T', ' '), '%Y-%m-%d %H:%M')
                submitted_date_text = submitted_on.strftime('%b %d, %Y %H:%M')

            # --- SAFETY NET 2: Fix the Decimal JSON Crash ---
            p_score = act['plagiarism_score']
            if p_score is not None:
                p_score = float(p_score) # This stops jsonify from crashing!

            # --- Check Status ---
            status = "Missing"
            if act['submission_id']:
                status = "Submitted"
            elif due_date > now:
                status = "Pending"
            
            audit_data.append({
                'title': act['title'],
                'due_date': due_date.strftime('%b %d, %Y %H:%M'),
                'status': status,
                'submitted_on': submitted_date_text,
                'plagiarism_score': p_score 
            })

        return jsonify({'success': True, 'student_name': student['fullname'], 'audit': audit_data})

    except Exception as e:
        import traceback
        traceback.print_exc()
        return jsonify({'success': False, 'error': str(e)}), 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== LECTURER PROFILE ======================
@app.route('/student/api/lecturer_profile/<int:course_id>', methods=['GET'])
def get_lecturer_profile(course_id):
    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)

        # Updated query to grab the new profile details!
        query = """
            SELECT u.fullname as name, c.course_name, u.email, 
                   lp.office_room, lp.phone_number, lp.consultation_hours
            FROM courses c
            LEFT JOIN users u ON u.fullname LIKE CONCAT(c.lecturer, '%%') AND u.role = 'lecturer'
            LEFT JOIN lecturer_profiles lp ON u.username = lp.username
            WHERE c.id = %s
        """
        cursor.execute(query, (course_id,))
        lecturer = cursor.fetchone()

        if lecturer:
            return jsonify({'success': True, 'profile': lecturer})
        return jsonify({'success': False, 'error': 'Course not found.'})

    except Exception as e:
        import traceback
        traceback.print_exc()
        return jsonify({'success': False, 'error': str(e)}), 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== NOTIFICATIONS & REMINDER ======================
@app.route('/student/api/notifications/<int:course_id>', methods=['GET'])
def get_student_notifications(course_id):
    if 'username' not in session:
        return jsonify({'success': False, 'error': 'Unauthorized'})
        
    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)
        username = session['username']

        # Find all activities for this course that the student HAS NOT submitted yet
        query = """
            SELECT a.title, a.due_date 
            FROM activities a
            LEFT JOIN submissions s ON a.id = s.activity_id AND s.student_username = %s
            WHERE a.course_id = %s AND s.submission_id IS NULL
            ORDER BY a.due_date ASC
        """
        cursor.execute(query, (username, course_id))
        pending_tasks = cursor.fetchall()

        now = datetime.now()
        reminders = []
        
        for task in pending_tasks:
            due_date = task['due_date']
            if isinstance(due_date, str):
                due_date = datetime.strptime(due_date[:16].replace('T', ' '), '%Y-%m-%d %H:%M')
            
            # Determine if it's coming up or already late
            if due_date < now:
                status = "OVERDUE"
            else:
                days_left = (due_date - now).days
                status = f"Due in {days_left} days" if days_left > 0 else "Due TODAY"

            reminders.append({
                'title': task['title'],
                'due_date': due_date.strftime('%b %d, %Y %I:%M %p'),
                'status': status,
                'is_overdue': due_date < now
            })

        return jsonify({'success': True, 'reminders': reminders})

    except Exception as e:
        import traceback
        traceback.print_exc()
        return jsonify({'success': False, 'error': str(e)}), 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== REDIRECTS LECT DASHBOARD ======================
@app.route('/lecturer/dashboard', methods=['GET'])
def lecturer_dashboard_redirect():
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/')

    lecturer_username_session = session['username'] 
    db_conn = get_db()
    cursor = db_conn.cursor(dictionary=True)

    # Fetch user info (needed for the next query)
    cursor.execute("SELECT fullname FROM users WHERE username=%s", (lecturer_username_session,))
    user = cursor.fetchone()

    if not user:
         return redirect('/logout')

    # Assuming 'courses.lecturer' stores the first name (e.g., 'Ayati')
    lecturer_name_db = user['fullname'].split(' ')[0]

    # Find the ID of the first course the lecturer teaches
    cursor.execute("SELECT id AS course_id FROM courses WHERE lecturer = %s LIMIT 1", (lecturer_name_db,)) 
    first_course = cursor.fetchone()

    cursor.close()
    db_conn.close()

    if first_course:
        course_id = first_course['course_id']
        # Redirects to the specific dashboard view
        return redirect(f'/lecturer/dashboard/{course_id}')
    else:
        return "You are logged in, but you are not assigned to any courses.", 200

# ====================== LECTURER IND ACTIVITY (SMART UN-MUTE FIX) ======================
@app.route('/lecturer/activities/individual/<int:course_id>', methods=['GET'])
def lecturer_view_individual_activities(course_id):
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/')

    db_conn = get_db()
    cursor = db_conn.cursor(dictionary=True) 

    # 1. Get user/lecturer info
    cursor.execute("SELECT fullname FROM users WHERE username = %s", (session.get('username'),))
    user = cursor.fetchone() 

    # 2. Get course info
    cursor.execute("SELECT course_code, course_name FROM courses WHERE id = %s", (course_id,))
    course = cursor.fetchone()

    # 3. Get activities
    cursor.execute("SELECT * FROM activities WHERE course_id = %s AND type = 'individual' ORDER BY due_date ASC", (course_id,))
    activities = cursor.fetchall()
    
    # 🚨 FIXED: Fetch BOTH the activity_id AND the alert_count from the acknowledged table
    cursor.execute("SELECT activity_id, alert_count FROM acknowledged_tampers")
    # Store it as a dictionary so we can easily look up the count: {activity_id: alert_count}
    acknowledged_data = {row['activity_id']: row['alert_count'] for row in cursor.fetchall()}

    cursor.close()
    db_conn.close()

    # ==========================================
    # Smart Auto-Categorization
    # ==========================================
    categorized_activities = { 'Assignments': [], 'Projects': [], 'Labs': [], 'Other': [] }
    
    for act in activities:
        title_lower = act['title'].lower()
        if 'assignment' in title_lower: categorized_activities['Assignments'].append(act)
        elif 'project' in title_lower: categorized_activities['Projects'].append(act)
        elif 'lab' in title_lower: categorized_activities['Labs'].append(act)
        else: categorized_activities['Other'].append(act)

    # ---> THE NEW DASHBOARD FIX: Smart Un-Muting <---
    any_activity_tampered = False
    hacked_activities = [] 

    if activities:
        for act in activities:
            # 1. Check if the activity is tampered
            if check_activity_tampering(act['id'], check_scores=False, check_title=True, check_files=True, check_due_date=True):
                
                # 2. Calculate how many alerts exist RIGHT NOW for this activity
                # We need a quick way to count the errors. For now, we will simulate a count 
                # by re-running a slightly more detailed check, or by simply assuming that if 
                # check_activity_tampering returns True, there is at least 1 error.
                
                # To make this truly robust, we should calculate the exact number of errors.
                # Let's run a quick "mini-audit" to get the exact count of current errors:
                current_error_count = get_tamper_alert_count(act['id']) 
                
                # 3. Check against the acknowledged table
                acknowledged_count = acknowledged_data.get(act['id'], 0) # Defaults to 0 if never acknowledged
                
                # 🚨 THE CRITICAL FIX: Only trigger the banner if the current errors are GREATER than the acknowledged errors!
                if current_error_count > acknowledged_count:
                    any_activity_tampered = True
                    hacked_activities.append({'id': act['id'], 'title': act['title']})

    return render_template('individual_activity_lecturer.html',
                           user=user,         
                           course=course,     
                           course_id=course_id,
                           activities=activities, 
                           categorized_activities=categorized_activities, 
                           now=datetime.now(),
                           db_tampered=any_activity_tampered,
                           hacked_activities=hacked_activities, 
                           activity_id=hacked_activities[0]['id'] if len(hacked_activities) == 1 else None
                          )

# ====================== CREATE ACTIVITY (FULL SECURITY INTEGRATION) ======================
@app.route("/lecturer/create_activity", methods=['POST'])
def create_activity():
    if 'user_id' not in session or session.get('role') != 'lecturer':
        return redirect('/logout')

    # 1. Get ALL the necessary form data
    course_id = request.form.get('course_id')
    activity_type = request.form.get('activity_type', 'individual')
    title = request.form.get('title')
    description = request.form.get('description')
    due_date = request.form.get('due_date')
    
    db_conn = None
    cursor = None
    
    try:
        db_conn = get_db()
        cursor = db_conn.cursor()

        # 2. Insert full data into the SQL Database
        query = """
        INSERT INTO activities (
            course_id, title, description, type, due_date
        ) VALUES (%s, %s, %s, %s, %s)
        """
        cursor.execute(query, (course_id, title, description, activity_type, due_date))
        
        # 3. Capture the newly generated Activity ID (Crucial for the Blockchain!)
        new_activity_id = cursor.lastrowid
        
        db_conn.commit()

        # ==========================================================
        # 🚨 BLOCKCHAIN SYNCHRONIZATION: Establish the Baseline 
        # ==========================================================
        activity_chain = Blockchain(identifier=new_activity_id) 
        activity_chain.new_log(
            sender=session.get('username'),
            recipient=new_activity_id, 
            event_type="ACTIVITY_CREATED", 
            # Log BOTH the Title and Due Date to secure them from the very beginning
            details=f"Title: {title} | DueDate: {due_date}" 
        )

        # Mine the block to permanently seal the creation
        last_proof = activity_chain.last_block['proof']
        proof = activity_chain.proof_of_work(last_proof)
        activity_chain.new_block(proof)
        # ==========================================================

        flash('Activity successfully created and secured on the ledger!', 'success')
        return redirect(f'/lecturer/activities/individual/{course_id}')

    except Exception as e:
        if db_conn: db_conn.rollback() # Always rollback SQL on failure
        print(f"\n{'='*50}\nCRITICAL CREATION ERROR: {e}\n{'='*50}\n")
        flash(f"Error creating activity: {e}", "danger")
        
        # Fallback redirect in case of error
        return redirect(request.referrer or f'/lecturer/activities/individual/{course_id}')
        
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== EDIT ACTIVITY (SECURED) ======================
@app.route('/lecturer/edit_activity/<int:activity_id>', methods=['POST'])
@lecturer_required
def edit_activity(activity_id):
    db_conn = None
    cursor = None
    try:
        # Get the updated data from the form
        title = request.form.get('task_title')
        description = request.form.get('description')
        due_date = request.form.get('due_date')
        course_id = request.form.get('course_id')

        db_conn = get_db()
        cursor = db_conn.cursor()

        # Update the activity in the database
        update_query = """
            UPDATE activities 
            SET title = %s, description = %s, due_date = %s 
            WHERE id = %s
        """
        cursor.execute(update_query, (title, description, due_date, activity_id))
        db_conn.commit()

        # ==========================================================
        # 🚨 BLOCKCHAIN SYNCHRONIZATION: Log the Edit 
        # ==========================================================
        # This prevents the tamper alarm from triggering after a legitimate edit
        activity_chain = Blockchain(identifier=activity_id) 
        activity_chain.new_log(
            sender=session.get('username'),
            recipient=activity_id, 
            event_type="ACTIVITY_EDITED", 
            # ✅ THE FIX: Log BOTH the Title and the Due Date into the immutable ledger
            details=f"Title: {title} | DueDate: {due_date}" 
        )

        # Mine the block to permanently seal the legitimate edit
        last_proof = activity_chain.last_block['proof']
        proof = activity_chain.proof_of_work(last_proof)
        activity_chain.new_block(proof)
        # ==========================================================

        flash('Activity updated successfully!', 'success')
        return redirect(f'/lecturer/activities/individual/{course_id}')

    except Exception as e:
        if db_conn: db_conn.rollback() # Always rollback on error
        import traceback
        traceback.print_exc()
        flash(f'An error occurred while updating the activity: {e}', 'danger')
        return redirect(request.referrer)
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== VIEW SUBMISSION ======================
@app.route('/lecturer/view_submissions/<int:activity_id>', methods=['GET'])
@lecturer_required
def lecturer_view_submissions(activity_id):
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/')

    db_conn = get_db()
    cursor = db_conn.cursor(dictionary=True)

    # Fetch the lecturer's full name for the sidebar
    cursor.execute("SELECT fullname FROM users WHERE username = %s", (session.get('username'),))
    current_user = cursor.fetchone()

    # 1. Fetch Activity Details
    cursor.execute("""
        SELECT a.title, a.description, a.due_date, a.course_id, c.course_code, c.course_name
        FROM activities a
        JOIN courses c ON a.course_id = c.id
        WHERE a.id = %s
    """, (activity_id,))
    activity = cursor.fetchone()

    if not activity:
        cursor.close()
        db_conn.close()
        return "Activity not found.", 404

    # 2. Fetch all Submissions
    cursor.execute("""
        SELECT s.*, u.fullname AS student_name
        FROM submissions s
        JOIN users u ON s.student_username = u.username
        WHERE s.activity_id = %s
        ORDER BY s.submitted_on DESC
    """, (activity_id,))
    submissions = cursor.fetchall()
    
    cursor.close()
    db_conn.close()

    # 3. ---> NEW: LIGHTWEIGHT BACKGROUND TAMPER CHECK <---
    db_tampered = False
    try:
        import re
        activity_chain = Blockchain(identifier=activity_id)
        
        # Extract DB scores to compare
        db_scores = {sub['submission_id']: sub['plagiarism_score'] for sub in submissions if sub['plagiarism_score'] is not None}
        latest_chain_scores = {}

        # Extract latest Chain scores
        for block in activity_chain.chain:
            for log in block.get('logs', []):
                if log['event_type'] == 'SCORE_LOCKED':
                    match = re.search(r"Sub_ID:(\d+)\s*\|\s*Score:([\d\.]+)", log['details'])
                    if match:
                        latest_chain_scores[int(match.group(1))] = float(match.group(2))

        # Compare! If even one score is manipulated, flip the alarm switch to True
        for sub_id, chain_score in latest_chain_scores.items():
            db_score = db_scores.get(sub_id)
            if db_score is not None and abs(chain_score - float(db_score)) > 0.01:
                db_tampered = True
                break # We only need one mismatch to trigger the banner
    except Exception as e:
        print(f"Background blockchain verification error: {e}")

    return render_template('view_submissions_lecturer.html',
                           activity=activity,
                           activity_id=activity_id,
                           submissions=submissions,
                           user=current_user,
                           db_tampered=db_tampered # ---> PASS THE ALARM STATUS TO HTML
                           )

# ====================== DELETE ACTIVITY (FIXED) ======================
@app.route('/lecturer/delete_activity/<int:activity_id>', methods=['POST'])
def lecturer_delete_activity(activity_id):
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/')

    db_conn = None # Initialize db_conn outside try/except
    cursor = None # FIX: Initialize cursor outside try/except to prevent NameError in finally block
    course_id = None
    
    try:
        db_conn = get_db()
        cursor = db_conn.cursor() # Now cursor is defined

        # 1. Get Course ID for redirection 
        cursor.execute("SELECT course_id FROM activities WHERE id = %s", (activity_id,))
        result = cursor.fetchone()
        if result:
            course_id = result[0]
        else:
            flash('Error: Activity not found.', 'danger')
            return redirect('/lecturer/dashboard') 
        
        # 2. Delete ALL submissions associated with this activity (CRITICAL STEP)
        cursor.execute("DELETE FROM submissions WHERE activity_id = %s", (activity_id,))
        
        # 3. Delete the activity itself
        cursor.execute("DELETE FROM activities WHERE id = %s", (activity_id,))
        
        db_conn.commit()
        
        # === BLOCKCHAIN INTEGRATION START ===
        
        # FIX: Instantiate the Blockchain object (Was missing, causing NameError)
        activity_chain = Blockchain(identifier=activity_id)
        
        # 1. Add the log (transaction) to the pending list
        activity_chain.new_log(
            sender=session['username'],
            recipient=activity_id, # Log recipient is the deleted activity ID
            event_type="ACTIVITY_DELETED",
            details=f"Activity ID {activity_id} and all related submissions removed."
        )
        
        # 2. Mine a new block to seal the log (Proof-of-Work simulation)
        last_proof = activity_chain.last_block['proof']
        proof = activity_chain.proof_of_work(last_proof)
        activity_chain.new_block(proof)
        
        print(f"=== BLOCKCHAIN LOGGED === New Block Mined! Index: {activity_chain.last_block['index']} | Event: ACTIVITY_DELETED\n")
        # ==================================
        
        flash('Activity and all submissions successfully deleted.', 'success')

    except Exception as e:
        if db_conn:
             db_conn.rollback() # Rollback only if db_conn exists
        print(f"Error deleting activity: {e}")
        flash('Error deleting activity. Check server logs.', 'danger') #

    finally:
        # Check if cursor and db_conn were successfully created before closing
        if cursor:
             cursor.close()
        if db_conn:
            db_conn.close()
        
    if course_id:
        return redirect(f'/lecturer/activities/individual/{course_id}')
    else:
        return redirect('/lecturer/dashboard')
    

# ====================== DOWNLOAD STUDENT SUBMISSION ======================
@app.route('/download/submission/<int:submission_id>')
def download_submission(submission_id):
    db_conn = get_db()
    cursor = db_conn.cursor(dictionary=True)
    cursor.execute("SELECT file_name FROM submissions WHERE submission_id = %s", (submission_id,))
    sub = cursor.fetchone()
    cursor.close()
    db_conn.close()
    
    if sub:
        return send_from_directory(app.config['UPLOAD_FOLDER'], sub['file_name'], as_attachment=True)
    return "File not found", 404

# ====================== DOWNLOAD LECTURER TASK FILE ======================
@app.route('/download/task/<int:activity_id>')
def download_task_file(activity_id):
    if 'username' not in session:
        return redirect('/login')

    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)
        
        # Look up the specific activity to get the file name
        cursor.execute("SELECT file_name FROM activities WHERE id = %s", (activity_id,))
        activity = cursor.fetchone()
        
        if activity and activity['file_name']:
            # Serve the file securely from the task uploads folder!
            return send_from_directory(app.config['TASK_UPLOAD_FOLDER'], activity['file_name'], as_attachment=True)
        else:
            flash("No task file is attached to this activity.", "warning")
            return redirect(request.referrer or '/')

    except Exception as e:
        import traceback
        traceback.print_exc()
        return f"Error downloading file: {e}", 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== LECTURER DOWNLOAD REPORT ======================

@app.route('/lecturer/download_plagiarism_report/<int:target_id>')
@lecturer_required
def download_plagiarism_report(target_id):
    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)

        # 1. Fetch Primary Document
        cursor.execute("""
            SELECT s.*, u.fullname, s.activity_id 
            FROM submissions s 
            JOIN users u ON s.student_username = u.username 
            WHERE s.submission_id = %s
        """, (target_id,))
        target = cursor.fetchone()

        if not target:
            return "Submission not found", 404

        # 2. Fetch all other submissions
        cursor.execute("""
            SELECT s.*, u.fullname 
            FROM submissions s 
            JOIN users u ON s.student_username = u.username 
            WHERE s.submission_id IN (
                SELECT MAX(submission_id) 
                FROM submissions 
                WHERE activity_id = %s 
                GROUP BY student_username
            ) AND s.submission_id != %s
        """, (target['activity_id'], target_id))  # Use submission_id for the student route!
        all_other_submissions = cursor.fetchall()

        t_text = target['extracted_text'] or ""
        comparisons = []
        overall_max_score = 0.0

        # 3. Calculate Scores
        for other_sub in all_other_submissions:
            s_text = other_sub['extracted_text'] or ""
            score, matches = calculate_unified_similarity(t_text, s_text)
            
            if score > overall_max_score:
                overall_max_score = score
                
            if score >= 0.1:
                comparisons.append({
                    'other_sub': other_sub,
                    'score': score,
                    'matches': matches
                })

        comparisons.sort(key=lambda x: x['score'], reverse=True)
        sidebar_matches = []
        char_marks = [0] * len(t_text)

        # 4. Map the highlights exactly like the web view
        for comp in comparisons:
            source_num = len(sidebar_matches) + 1
            sidebar_matches.append({
                'source_name': comp['other_sub']['fullname'],
                'score': round(comp['score'], 1)
            })
            for m in comp['matches']:
                for i in range(m.a, m.a + m.size):
                    if i < len(char_marks) and char_marks[i] == 0:
                        char_marks[i] = source_num

        # Build Highlighted HTML
        full_html_parts = []
        if len(t_text) > 0:
            current_source = char_marks[0]
            current_text = t_text[0]
            for i in range(1, len(t_text)):
                if char_marks[i] != current_source:
                    if current_source != 0:
                        full_html_parts.append(f'<span class="match-source-{current_source}">{current_text}<sup class="source-tag">[{current_source}]</sup></span>')
                    else:
                        full_html_parts.append(current_text)
                    current_source = char_marks[i]
                    current_text = t_text[i]
                else:
                    current_text += t_text[i]

            if current_source != 0:
                full_html_parts.append(f'<span class="match-source-{current_source}">{current_text}<sup class="source-tag">[{current_source}]</sup></span>')
            else:
                full_html_parts.append(current_text)

        full_html = "".join(full_html_parts).replace('\n', '<br>')

        # 5. Render to a special PDF HTML template
       # Render PDF Template
        rendered_html = render_template('pdf_report_template.html', 
                                        target_name=target['fullname'],
                                        overall_score=round(overall_max_score, 1), 
                                        matches=sidebar_matches,
                                        content=full_html,
                                        now=datetime.now().strftime("%B %d, %Y"))

        if platform.system() == 'Windows':
            path_wkhtmltopdf = r'C:\Program Files\wkhtmltopdf\bin\wkhtmltopdf.exe'
        else:
            # Point to the newly extracted generic static binary!
            path_wkhtmltopdf = os.path.join(os.getcwd(), 'wkhtmltox', 'bin', 'wkhtmltopdf')
            
        config = pdfkit.configuration(wkhtmltopdf=path_wkhtmltopdf)

        # Options to make the PDF look like a clean A4 document
        options = {
            'page-size': 'A4',
            'margin-top': '0.75in',
            'margin-right': '0.75in',
            'margin-bottom': '0.75in',
            'margin-left': '0.75in',
            'encoding': "UTF-8",
            'no-outline': None
        }

        pdf = pdfkit.from_string(rendered_html, False, configuration=config, options=options)

        response = make_response(pdf)
        response.headers['Content-Type'] = 'application/pdf'
        response.headers['Content-Disposition'] = f'attachment; filename=Plagiarism_Report_{target["fullname"].replace(" ", "_")}.pdf'
        return response

    except Exception as e:
        import traceback
        traceback.print_exc()
        return f"Error Generating PDF: {e}", 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== LECTURER SEND REPORT ======================
@app.route('/lecturer/send_report/<int:target_id>', methods=['POST'])
@lecturer_required
def send_report_to_student(target_id):
    db_conn = None
    cursor = None
    try:
        lecturer_comment = request.form.get('lecturer_comment', '')
        
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)

        # 1. Fetch submission to make sure it exists
        cursor.execute("SELECT activity_id, extracted_text FROM submissions WHERE submission_id = %s", (target_id,))
        target = cursor.fetchone()

        # 2. THE FIX: Fetch only the LATEST other submissions to calculate the score against
        cursor.execute("""
            SELECT s.*, u.fullname 
            FROM submissions s 
            JOIN users u ON s.student_username = u.username 
            WHERE s.submission_id IN (
                SELECT MAX(submission_id) 
                FROM submissions 
                WHERE activity_id = %s 
                GROUP BY student_username
            ) AND s.submission_id != %s
        """, (target['activity_id'], target_id))
        all_other_submissions = cursor.fetchall()

        overall_max_score = 0.0
        t_text = target['extracted_text'] or ""
        
        for other_sub in all_other_submissions:
            s_text = other_sub['extracted_text'] or ""
            score, _ = calculate_unified_similarity(t_text, s_text)
            if score > overall_max_score:
                overall_max_score = score

        # 3. Save to the new shared_reports table
        cursor.execute("""
            INSERT INTO shared_reports (submission_id, similarity_score, lecturer_comment, shared_on) 
            VALUES (%s, %s, %s, NOW())
        """, (target_id, round(overall_max_score, 1), lecturer_comment))
        
        db_conn.commit()

        # ---> NEW BLOCKCHAIN IMPROVEMENT <---
        # Notarize the exact score and feedback given to the student!
        try:
            from local_blockchain import Blockchain
            activity_chain = Blockchain(identifier=target['activity_id'])
            activity_chain.new_log(
                sender=session['username'],
                recipient=target['activity_id'],
                event_type="REPORT_PUBLISHED",
                details=f"Lecturer published Originality Report for Submission #{target_id}. Final Score: {round(overall_max_score, 1)}%."
            )
            activity_chain.new_block(activity_chain.proof_of_work(activity_chain.last_block['proof']))
        except Exception as chain_error:
            print(f"Blockchain Error: {chain_error}")
        # ------------------------------------

        flash("Report successfully published to the student's dashboard!", "success")
    
        # 🚨 THE FIX: Change this redirect to point back to the Originality Report!
        return redirect(f'/lecturer/originality_report/{target_id}')

    except Exception as e:
        import traceback
        traceback.print_exc()
        return f"Database Error: {e}", 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# =================SEND / UPDATE REPORTS TO ALL STUDENTS=================
@app.route('/lecturer/send_all_reports/<int:activity_id>', methods=['POST'])
def send_all_reports(activity_id):
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/')
        
    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        # FIX 1: Add buffered=True to automatically clear results and prevent "Unread result" errors
        cursor = db_conn.cursor(dictionary=True, buffered=True)

        # 1. Fetch all submissions that have a saved score
        cursor.execute("""
            SELECT submission_id, plagiarism_score 
            FROM submissions 
            WHERE activity_id = %s AND plagiarism_score IS NOT NULL
        """, (activity_id,))
        submissions = cursor.fetchall()

        if not submissions:
            flash("No saved scores found! Please ensure the system has saved the plagiarism scores to the database.", "danger")
            return redirect(f'/lecturer/matrix_report/{activity_id}')

        reports_inserted = 0
        reports_updated = 0
        
        for sub in submissions:
            sub_id = sub['submission_id']
            score = sub['plagiarism_score']

            # Check if this specific submission already has a shared report
            cursor.execute("SELECT submission_id FROM shared_reports WHERE submission_id = %s", (sub_id,))
            # FIX 2: Use fetchall() instead of fetchone() to completely empty the database buffer!
            existing = cursor.fetchall()

            if not existing:
                # INSERT: First time publishing this report
                cursor.execute("""
                    INSERT INTO shared_reports (submission_id, similarity_score, lecturer_comment, shared_on) 
                    VALUES (%s, %s, %s, NOW())
                """, (sub_id, float(score), 'Automated Matrix Batch Report'))
                reports_inserted += 1
            else:
                # UPDATE: Lecturer clicked publish again, update the existing report
                cursor.execute("""
                    UPDATE shared_reports 
                    SET similarity_score = %s, shared_on = NOW()
                    WHERE submission_id = %s
                """, (float(score), sub_id))
                reports_updated += 1

        db_conn.commit()

        # Dynamic Success Banners
        if reports_inserted > 0 and reports_updated > 0:
            flash(f"Successfully published {reports_inserted} new report(s) and updated {reports_updated} existing report(s)!", "success")
        elif reports_inserted > 0:
            flash(f"Successfully published {reports_inserted} report(s) to the student dashboards!", "success")
        elif reports_updated > 0:
            flash(f"Successfully refreshed and updated {reports_updated} existing student report(s)!", "info")
        else:
            flash("No submissions were found to publish.", "warning")

    except Exception as e:
        if db_conn: db_conn.rollback()
        import traceback
        traceback.print_exc()
        flash(f"Database Error: {e}", "danger")
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

    return redirect(f'/lecturer/matrix_report/{activity_id}')

# ====================== STUDENT RECEIVE REPORT (COURSE SPECIFIC) ======================
@app.route('/student/my_reports/<int:course_id>')
def student_reports(course_id):
    if 'username' not in session or session.get('role') != 'student':
        return redirect('/')

    student_username = session.get('username') 
    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)

        # 1. Fetch user details for the sidebar
        cursor.execute("SELECT fullname FROM users WHERE username = %s", (student_username,))
        user_data = cursor.fetchone()

        # 2. Fetch specific course details for the page header
        cursor.execute("SELECT course_code, course_name FROM courses WHERE id = %s", (course_id,))
        course_data = cursor.fetchone()

        # 3. THE FIX: Filter the SQL query using `AND c.id = %s`
        query = """
            SELECT sr.*, s.activity_id, a.title, c.course_code, c.course_name 
            FROM shared_reports sr
            JOIN submissions s ON sr.submission_id = s.submission_id
            JOIN activities a ON s.activity_id = a.id
            JOIN courses c ON a.course_id = c.id
            WHERE s.student_username = %s AND c.id = %s
            ORDER BY sr.shared_on DESC
        """
        cursor.execute(query, (student_username, course_id))
        reports = cursor.fetchall()

        return render_template('student_reports.html', reports=reports, user=user_data, course=course_data)

    except Exception as e:
        import traceback
        traceback.print_exc()
        return f"Error: {e}", 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ==========================================
# NEW ROUTE: Student PDF Download
# ==========================================
@app.route('/student/download_report/<int:submission_id>')
# @student_required
def student_download_report(submission_id):
    student_username = session.get('username')
    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)

        # 1. Fetch document AND verify it belongs to this specific student
        cursor.execute("""
            SELECT s.*, u.fullname, s.activity_id 
            FROM submissions s 
            JOIN users u ON s.student_username = u.username 
            WHERE s.submission_id = %s AND s.student_username = %s
        """, (submission_id, student_username))
        target = cursor.fetchone()

        if not target:
            return "Unauthorized or Submission not found", 403

        # 2. Re-run the exact same calculation logic used in the lecturer download
        cursor.execute("""
            SELECT s.*, u.fullname 
            FROM submissions s 
            JOIN users u ON s.student_username = u.username 
            WHERE s.submission_id IN (
                SELECT MAX(submission_id) 
                FROM submissions 
                WHERE activity_id = %s 
                GROUP BY student_username
            ) AND s.submission_id != %s
        """, (target['activity_id'], submission_id))  # ✅ CHANGED: target_id to submission_id
        all_other_submissions = cursor.fetchall()

        t_text = target['extracted_text'] or ""
        comparisons = []
        overall_max_score = 0.0

        for other_sub in all_other_submissions:
            s_text = other_sub['extracted_text'] or ""
            score, matches = calculate_unified_similarity(t_text, s_text)
            if score > overall_max_score: overall_max_score = score
            if score >= 0.1: comparisons.append({'other_sub': other_sub, 'score': score, 'matches': matches})

        comparisons.sort(key=lambda x: x['score'], reverse=True)
        sidebar_matches = []
        char_marks = [0] * len(t_text)

        for comp in comparisons:
            source_num = len(sidebar_matches) + 1
            sidebar_matches.append({'source_name': comp['other_sub']['fullname'], 'score': round(comp['score'], 1)})
            for m in comp['matches']:
                for i in range(m.a, m.a + m.size):
                    if i < len(char_marks) and char_marks[i] == 0: char_marks[i] = source_num

        full_html_parts = []
        if len(t_text) > 0:
            current_source, current_text = char_marks[0], t_text[0]
            for i in range(1, len(t_text)):
                if char_marks[i] != current_source:
                    if current_source != 0: full_html_parts.append(f'<span class="match-source-{current_source}">{current_text}<sup class="source-tag">[{current_source}]</sup></span>')
                    else: full_html_parts.append(current_text)
                    current_source, current_text = char_marks[i], t_text[i]
                else: current_text += t_text[i]
            if current_source != 0: full_html_parts.append(f'<span class="match-source-{current_source}">{current_text}<sup class="source-tag">[{current_source}]</sup></span>')
            else: full_html_parts.append(current_text)

        full_html = "".join(full_html_parts).replace('\n', '<br>')

        # Render PDF Template
        rendered_html = render_template('pdf_report_template.html', 
                                        target_name=target['fullname'],
                                        overall_score=round(overall_max_score, 1), 
                                        matches=sidebar_matches,
                                        content=full_html,
                                        now=datetime.now().strftime("%B %d, %Y"))

        if platform.system() == 'Windows':
            path_wkhtmltopdf = r'C:\Program Files\wkhtmltopdf\bin\wkhtmltopdf.exe'
        else:
            # Point to the newly extracted generic static binary!
            path_wkhtmltopdf = os.path.join(os.getcwd(), 'wkhtmltox', 'bin', 'wkhtmltopdf')
            
        config = pdfkit.configuration(wkhtmltopdf=path_wkhtmltopdf)

        # Options to make the PDF look like a clean A4 document
        options = {
            'page-size': 'A4',
            'margin-top': '0.75in',
            'margin-right': '0.75in',
            'margin-bottom': '0.75in',
            'margin-left': '0.75in',
            'encoding': "UTF-8",
            'no-outline': None
        }

        pdf = pdfkit.from_string(rendered_html, False, configuration=config, options=options)

        response = make_response(pdf)
        response.headers['Content-Type'] = 'application/pdf'
        response.headers['Content-Disposition'] = f'attachment; filename=My_Originality_Report_{target["fullname"].replace(" ", "_")}.pdf'
        return response

    except Exception as e:
        import traceback
        traceback.print_exc()
        return f"Error Generating PDF: {e}", 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== VIEW ORIGINALITY REPORT ======================
@app.route('/lecturer/originality_report/<int:target_id>')
@lecturer_required
def originality_report(target_id):
    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)

        # ---> THE BULLETPROOF SIDEBAR FIX <---
        # Fetch the name, but provide a safe fallback dictionary if it fails
        cursor.execute("SELECT fullname FROM users WHERE username = %s", (session.get('username'),))
        user_record = cursor.fetchone()
        current_user = user_record if user_record else {'fullname': 'Lecturer Name'}

        # 1. Fetch the Primary Document (AND THE ACTIVITY ID!)
        cursor.execute("""
            SELECT s.*, u.fullname, s.activity_id 
            FROM submissions s 
            JOIN users u ON s.student_username = u.username 
            WHERE s.submission_id = %s
        """, (target_id,))
        target = cursor.fetchone()

        if not target:
            return "Submission not found", 404

        # 🚨 THE NEW VARIABLE: Store the activity ID safely
        activity_id = target['activity_id']

        # 2. Fetch all OTHER latest submissions to compare against
        cursor.execute("""
            SELECT s.*, u.fullname 
            FROM submissions s 
            JOIN users u ON s.student_username = u.username 
            WHERE s.submission_id IN (
                SELECT MAX(submission_id) 
                FROM submissions 
                WHERE activity_id = %s 
                GROUP BY student_username
            ) AND s.submission_id != %s
        """, (target['activity_id'], target_id))
        all_other_submissions = cursor.fetchall()

        t_text = target['extracted_text'] or ""
        comparisons = []
        
        # Explicit tracking variable for the highest score
        highest_score = 0.0

        for other_sub in all_other_submissions:
            s_text = other_sub['extracted_text'] or ""
            score, matches = calculate_unified_similarity(t_text, s_text)
            
            if score > highest_score: 
                highest_score = score
                
            if score >= 0.1:
                comparisons.append({'other_sub': other_sub, 'score': score, 'matches': matches})

        comparisons.sort(key=lambda x: x['score'], reverse=True)
        sidebar_matches = []
        char_marks = [0] * len(t_text)

            for comp in comparisons:
            source_num = len(sidebar_matches) + 1
            sidebar_matches.append({'source_name': comp['other_sub']['fullname'], 'score': round(comp['score'], 1), 'sub_id': comp['other_sub']['submission_id']})
            for m in comp['matches']:
                for i in range(m.a, m.a + m.size):
                    if i < len(char_marks) and char_marks[i] == 0: 
                        # 🚨 THE FIX: Do not apply the highlight background to newlines!
                        if t_text[i] not in ['\n', '\r']:
                            char_marks[i] = source_num

        full_html_parts = []
        if len(t_text) > 0:
            current_source = char_marks[0]
            current_text = t_text[0]
            for i in range(1, len(t_text)):
                if char_marks[i] != current_source:
                    if current_source != 0: full_html_parts.append(f'<span class="match-source-{current_source}">{current_text}<sup class="source-tag">{current_source}</sup></span>')
                    else: full_html_parts.append(current_text)
                    current_source = char_marks[i]
                    current_text = t_text[i]
                else: current_text += t_text[i]
            if current_source != 0: full_html_parts.append(f'<span class="match-source-{current_source}">{current_text}<sup class="source-tag">{current_source}</sup></span>')
            else: full_html_parts.append(current_text)

        # ==========================================
        # 🚨 THE TEXT CLEANING FIX (STEP A)
        # ==========================================
        raw_html = "".join(full_html_parts)
        
        # 1. Shrink massive gaps (3 or more newlines) down to just 2 newlines
        cleaned_html = re.sub(r'\n{3,}', '\n\n', raw_html)
        
        # 2. We DO NOT use .replace('\n', '<br>') anymore! 
        # HTML <br> tags ruin original indents. We keep the raw '\n' characters 
        # and let the CSS on the frontend handle the formatting perfectly.
        full_html = cleaned_html

        # ---> CRITICAL FIX: Pass the activity_id to the HTML template! <---
        return render_template(
            'originality_report.html', 
            target_id=target_id, 
            target_name=target['fullname'], 
            overall_score=round(highest_score, 1), 
            matches=sidebar_matches, 
            content=full_html, 
            now=datetime.now().strftime("%B %d, %Y"),
            user=current_user,
            activity_id=activity_id  # 👈 This makes the back button work!
        )

    except Exception as e:
        import traceback
        traceback.print_exc()
        return f"Internal Error: {e}", 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ----------------------------------------------
# 1. VIEW STREAM PAGE
# ----------------------------------------------
@app.route("/lecturer/stream/<int:course_id>")
def lecturer_stream(course_id):
    # FIXED: Check for 'username' instead of 'user_id'
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/')

    lecturer_username_session = session['username'] 
    
    user = {}
    course = {}
    posts = []
    
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True) 

        # 1. Fetch Lecturer Details
        cursor.execute("SELECT fullname FROM users WHERE username=%s", (lecturer_username_session,))
        user_data = cursor.fetchone()
        if user_data:
            user = user_data 

        # 2. Fetch Course Details
        cursor.execute("SELECT course_name, course_code FROM courses WHERE id=%s", (course_id,))
        course_data = cursor.fetchone()
        if course_data:
            course = course_data 

        # 3. Fetch Posts (Including JOIN)
        cursor.execute("""
            SELECT 
                p.*, 
                u.fullname AS author_name 
            FROM posts p
            JOIN users u ON p.user_id = u.id
            WHERE p.course_id = %s
            ORDER BY p.created_at DESC
        """, (course_id,))
        
        posts = cursor.fetchall()
        
        cursor.close()
        db_conn.close()

    except Exception as e:
        print(f"--- LECTURER STREAM CRASHED ---: {e}") 
        
    return render_template(
        "stream.html", 
        user=user, 
        course=course, 
        course_id=course_id, 
        posts=posts 
    )

# ----------------------------------------------
# 2. API: GET STREAM CONTENT (For Auto-Refresh)
# ----------------------------------------------
@app.route("/api/get_stream_content/<int:course_id>")
def get_stream_content(course_id):
    # FIXED: Check for 'username' instead of 'user_id'
    if 'username' not in session:
        return "" # Return empty if not logged in

    posts = []
    
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True) 

        cursor.execute("""
            SELECT 
                p.*, 
                u.fullname AS author_name 
            FROM posts p
            JOIN users u ON p.user_id = u.id
            WHERE p.course_id = %s
            ORDER BY p.created_at DESC
        """, (course_id,))
        
        posts = cursor.fetchall()
        
        cursor.close()
        db_conn.close()

    except Exception as e:
        print(f"--- API FETCH CRASHED ---: {e}") 
        return "Failed to load posts due to server error.", 500

    return render_template(
        "stream_content.html", 
        posts=posts 
    )

# ----------------------------------------------
# 3. LECTURER POST ANNOUNCEMENT 
# ----------------------------------------------
@app.route('/lecturer/post', methods=['POST'])
def lecturer_post():
    # FIXED: Check for 'username' instead of 'user_id'
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/')

    try:
        course_id = request.form['course_id']
        post_content = request.form['post_content']
        username = session['username']

        db_conn = get_db()
        
        # We use dictionary=True to easily grab the ID
        cursor = db_conn.cursor(dictionary=True)

        # FIXED: We need to find this lecturer's integer ID to save the post properly
        cursor.execute("SELECT id FROM users WHERE username = %s", (username,))
        user_record = cursor.fetchone()
        
        if not user_record:
            return "User not found", 404
            
        lecturer_user_id = user_record['id']

        # Handle Timestamp 
        current_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')

        # Insert Post into Database
        query = """
        INSERT INTO posts (
            course_id, 
            user_id, 
            content, 
            created_at
        ) VALUES (%s, %s, %s, %s)
        """
        
        # We MUST use standard cursor for INSERT, so we close the dict cursor and open a normal one
        cursor.close()
        cursor = db_conn.cursor()
        
        cursor.execute(query, (
            course_id, 
            lecturer_user_id, 
            post_content,
            current_time
        ))
        
        db_conn.commit()
        cursor.close()
        db_conn.close()

        flash('Announcement successfully posted!', 'success')
        return redirect('/lecturer/dashboard') # Or wherever you redirect to

    except Exception as e:
        print(f"--- POST CREATION FAILED ---")
        print(f"MySQL/Python Error: {e}") 
        return "Error creating post. Check logs.", 500
    
# ----------------------------------------------
# STUDENT STREAM ROUTE
# ----------------------------------------------
@app.route("/student/stream/<int:course_id>")
def student_stream(course_id):
    # 1. Security Check: Must be a student!
    if 'username' not in session or session.get('role') != 'student':
        flash('Unauthorized access. Students only.', 'danger')
        return redirect('/login')

    student_username = session['username'] 
    
    course = {}
    posts = []
    
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True) 

        # 2. Fetch Course Details (To display the title at the top)
        cursor.execute("SELECT id, course_name, course_code FROM courses WHERE id=%s", (course_id,))
        course_data = cursor.fetchone()
        if course_data:
            course = course_data 

        # 3. Fetch Posts for this specific class
        cursor.execute("""
            SELECT 
                p.*, 
                u.fullname AS author_name 
            FROM posts p
            JOIN users u ON p.user_id = u.id
            WHERE p.course_id = %s
            ORDER BY p.created_at DESC
        """, (course_id,))
        
        posts = cursor.fetchall()
        
        cursor.close()
        db_conn.close()

    except Exception as e:
        print(f"--- STUDENT STREAM CRASHED ---: {e}") 
        
    # 4. Render the exact same HTML template! 
    # The HTML already knows to hide the post box from students.
    return render_template(
        "stream.html", 
        course=course, 
        course_id=course_id, 
        posts=posts 
    )

# ----------------------------------------------
# 1. VIEW "MANAGE ANNOUNCEMENTS" PAGE
# ----------------------------------------------
@app.route("/lecturer/course/<int:course_id>/manage_posts")
def manage_posts(course_id):
    if 'username' not in session or session.get('role') != 'lecturer':
        flash('Unauthorized access.', 'danger')
        return redirect('/login')

    username = session['username']
    course = {}
    posts = []
    current_user = {}

    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)

        # ---> THE FIX: Fetch the lecturer's full name for the sidebar <---
        cursor.execute("SELECT fullname FROM users WHERE username = %s", (username,))
        current_user = cursor.fetchone()

        # Get course info for the header
        cursor.execute("SELECT id, course_name, course_code FROM courses WHERE id=%s", (course_id,))
        course_data = cursor.fetchone()
        if course_data:
            course = course_data

        # Fetch ONLY the posts written by THIS specific lecturer for THIS course
        cursor.execute("""
            SELECT p.* FROM posts p
            JOIN users u ON p.user_id = u.id
            WHERE p.course_id = %s AND u.username = %s
            ORDER BY p.created_at DESC
        """, (course_id, username))
        
        posts = cursor.fetchall()
        
        cursor.close()
        db_conn.close()

    except Exception as e:
        print(f"--- MANAGE POSTS CRASHED ---: {e}")

    # ---> THE FIX: Pass `user=current_user` to the HTML <---
    return render_template("manage_posts.html", course=course, course_id=course_id, posts=posts, user=current_user)

# ----------------------------------------------
# 2. DELETE ANNOUNCEMENT ROUTE
# ----------------------------------------------
@app.route("/lecturer/post/delete/<int:post_id>", methods=['POST'])
def delete_post(post_id):
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/login')

    course_id = request.form.get('course_id')
    username = session['username']

    try:
        db_conn = get_db()
        cursor = db_conn.cursor()

        # HIGH SECURITY: The subquery ensures they can only delete the post if they are the true author!
        cursor.execute("""
            DELETE FROM posts 
            WHERE id = %s AND user_id = (SELECT id FROM users WHERE username = %s)
        """, (post_id, username))
        
        db_conn.commit()
        cursor.close()
        db_conn.close()

        flash('Announcement deleted successfully.', 'success')
    except Exception as e:
        print(f"--- DELETE FAILED ---: {e}")
        flash('Failed to delete announcement.', 'danger')

    return redirect(f"/lecturer/course/{course_id}/manage_posts")


# ----------------------------------------------
# 3. EDIT ANNOUNCEMENT ROUTE
# ----------------------------------------------
@app.route("/lecturer/post/edit/<int:post_id>", methods=['POST'])
def edit_post(post_id):
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/login')

    course_id = request.form.get('course_id')
    new_content = request.form.get('post_content')
    username = session['username']

    try:
        db_conn = get_db()
        cursor = db_conn.cursor()

        # HIGH SECURITY: Only update if the logged-in user is the original author
        cursor.execute("""
            UPDATE posts 
            SET content = %s 
            WHERE id = %s AND user_id = (SELECT id FROM users WHERE username = %s)
        """, (new_content, post_id, username))
        
        db_conn.commit()
        cursor.close()
        db_conn.close()

        flash('Announcement updated successfully.', 'success')
    except Exception as e:
        print(f"--- UPDATE FAILED ---: {e}")
        flash('Failed to update announcement.', 'danger')

    return redirect(f"/lecturer/course/{course_id}/manage_posts")

# ====================== LECTURER UPLOAD ACTIVITY (FIXED) ======================
@app.route('/lecturer/upload_activity', methods=['POST'])
def lecturer_upload_activity():
    if 'username' not in session or session.get('role') != 'lecturer':
        return redirect('/')

    # --- Data Retrieval ---
    # FIX: Dynamically grab the real course_id from the form instead of hardcoding it!
    course_id = request.form.get('course_id') 
    
    activity_title = request.form.get('task_title')      
    activity_type = request.form.get('activity_type')     
    activity_description = request.form.get('description') 
    due_date = request.form.get('due_date')             
    
    # Retrieve the uploaded file
    task_file = request.files.get('task_file')
    task_file_name_db = None 

    # --- Validation ---
    if not all([course_id, activity_title, activity_type, activity_description, due_date]):
        flash("Error: Required fields (Title, Description, or Due Date) are empty.", 'danger')
        return redirect(f'/lecturer/activities/individual/{course_id}')

    db_conn = None
    cursor = None
    new_activity_id = None
    save_path = None 
    
    try:
        db_conn = get_db()
        cursor = db_conn.cursor()

        # ==========================================
        # THE FIX: DUPLICATE TITLE CHECK
        # ==========================================
        # We use LOWER() so "Assignment 3" and "assignment 3" trigger the warning!
        cursor.execute("SELECT id FROM activities WHERE course_id = %s AND LOWER(title) = LOWER(%s)", (course_id, activity_title))
        if cursor.fetchone():
            flash(f'⚠️ Action Blocked: An activity named "{activity_title}" already exists. Please choose a unique title!', 'danger')
            cursor.close()
            db_conn.close()
            return redirect(f'/lecturer/activities/individual/{course_id}')
            
        # 1. Handle File Upload
        if task_file and task_file.filename:
            original_filename = secure_filename(task_file.filename)
            file_extension = os.path.splitext(original_filename)[1]
            
            timestamp = int(datetime.now().timestamp())
            task_file_name_db = f"task_{course_id}_{timestamp}{file_extension}"
            save_path = os.path.join(app.config["TASK_UPLOAD_FOLDER"], task_file_name_db)
            
            task_file.save(save_path)
            flash(f'Task file "{original_filename}" successfully uploaded.', 'info')

        # 2. Database Insertion
        query = """
        INSERT INTO activities (course_id, title, description, due_date, type, created_by, file_name)
        VALUES (%s, %s, %s, %s, %s, %s, %s)
        """
        
        cursor.execute(query, (
            course_id, 
            activity_title, 
            activity_description, 
            due_date, 
            activity_type,
            session.get('username'), 
            task_file_name_db        
        ))
        
        new_activity_id = cursor.lastrowid
        db_conn.commit()
        
        # 3. === BLOCKCHAIN INTEGRATION ===
        activity_chain = Blockchain(identifier=new_activity_id)
        
        details = f"Title: {activity_title}, Type: {activity_type}, File: {task_file_name_db or 'None'}"
        activity_chain.new_log(
            sender=session['username'], 
            recipient=new_activity_id, 
            event_type="ACTIVITY_CREATED",
            details=details
        )
        
        last_proof = activity_chain.last_block['proof']
        proof = activity_chain.proof_of_work(last_proof)
        activity_chain.new_block(proof)
        
        flash('Activity created and successfully logged to the immutable ledger!', 'success')
        
    except Exception as e:
        if task_file_name_db and save_path and os.path.exists(save_path):
            os.remove(save_path)
            
        if db_conn:
            db_conn.rollback()
            
        print(f"\n{'='*50}\nFINAL DIAGNOSTIC ERROR: {e}\n{'='*50}\n")
        flash(f"Error creating activity. Details: {e}", 'danger')
        
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()
            
    return redirect(f'/lecturer/activities/individual/{course_id}')

# ====================== LECTURER BLOCKCHAIN AUDIT (CROSS-VERIFICATION) ======================
@app.route('/lecturer/blockchain_audit_activity/<int:activity_id>', methods=['GET'])
@lecturer_required
def blockchain_audit_activity(activity_id):
    db_conn = None
    cursor = None
    try:
        activity_chain = Blockchain(identifier=activity_id)
        is_valid = activity_chain.is_chain_valid(activity_chain.chain)
        
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)
        
        cursor.execute("SELECT fullname FROM users WHERE username = %s", (session.get('username'),))
        user_record = cursor.fetchone()
        current_user = user_record if user_record else {'fullname': 'Lecturer Name'}

        cursor.execute("SELECT title, due_date, course_id FROM activities WHERE id = %s", (activity_id,))
        activity = cursor.fetchone()

        if not activity:
             flash("Activity not found.", 'danger')
             return redirect('/lecturer/dashboard')

        # 3. ---> THE ULTIMATE TAMPER DETECTION ENGINE <---
        import re
        db_tampered = False
        tamper_alerts = []

        # 🚨 FIXED: Get Database state WITH Student Names via JOIN
        cursor.execute("""
            SELECT s.submission_id, s.plagiarism_score, s.file_name, u.fullname 
            FROM submissions s
            JOIN users u ON s.student_username = u.username
            WHERE s.activity_id = %s
        """, (activity_id,))
        db_submissions = cursor.fetchall()
        
        # Create dictionaries mapping the ID to the score, and the ID to the student's name
        db_scores = {row['submission_id']: row['plagiarism_score'] for row in db_submissions if row['plagiarism_score'] is not None}
        db_names = {row['submission_id']: row['fullname'] for row in db_submissions}
        db_files = set(row['file_name'] for row in db_submissions if row['file_name'])

        # Get Blockchain State
        latest_chain_scores = {}
        latest_chain_title = None 
        latest_chain_due_date = None
        chain_active_files = set()

        for block in activity_chain.chain:
            for log in block.get('logs', []):
                if log['event_type'] == 'SCORE_LOCKED':
                    match = re.search(r"Sub_ID:(\d+)\s*\|\s*Score:([\d\.]+)", log['details'])
                    if match:
                        latest_chain_scores[int(match.group(1))] = float(match.group(2))
                
                elif log['event_type'] in ['ACTIVITY_CREATED', 'ACTIVITY_EDITED']:
                    match = re.search(r"Title:\s*(.+?)(?:\s*\||,\s*Type:|$)", log['details'])
                    if match:
                        latest_chain_title = match.group(1).strip()
                    
                    if "DueDate:" in log['details']:
                        try:
                            latest_chain_due_date = log['details'].split("DueDate:")[1].strip()
                        except IndexError:
                            pass
                        
                elif log['event_type'] == 'FILE_UPLOAD':
                    match = re.search(r"Student uploaded file:\s*(.+)", log['details'])
                    if match:
                        chain_active_files.add(match.group(1).strip())
                        
                elif log['event_type'] == 'FILE_DELETE':
                    match = re.search(r"Deleted file:\s*(.+)", log['details'])
                    if match:
                        filename_to_remove = match.group(1).strip()
                        if filename_to_remove in chain_active_files:
                            chain_active_files.remove(filename_to_remove)

        # 🚨 FIXED: CROSS-CHECK 1: SCORES (Now includes Student Name)
        for sub_id, chain_score in latest_chain_scores.items():
            db_score = db_scores.get(sub_id)
            student_name = db_names.get(sub_id, "Unknown Student")
            if db_score is not None and abs(chain_score - float(db_score)) > 0.01:
                db_tampered = True
                tamper_alerts.append(f"Submission #{sub_id} ({student_name}): Blockchain recorded {chain_score:.2f}%, but Database shows {float(db_score):.2f}%!")
                
        # CROSS-CHECK 2: ACTIVITY TITLE
        if latest_chain_title and activity['title'] != latest_chain_title:
            db_tampered = True
            tamper_alerts.append(f"Activity Title Tampered! Blockchain recorded '{latest_chain_title}', but Database shows '{activity['title']}'!")

        # CROSS-CHECK 3: FILE INTEGRITY
        for f in db_files:
            if f not in chain_active_files:
                db_tampered = True
                tamper_alerts.append(f"Ghost File Detected! '{f}' exists in Database but was never uploaded via Blockchain!")
                
        for f in chain_active_files:
            if f not in db_files:
                db_tampered = True
                tamper_alerts.append(f"Missing File Detected! '{f}' was recorded in Blockchain but secretly deleted from Database!")

        # CROSS-CHECK 4: DUE DATE
        if latest_chain_due_date and activity.get('due_date'):
            sql_date_raw = activity['due_date']
            
            # Use the new function instead of !=
            if compare_dates_safely(latest_chain_due_date, sql_date_raw):
                db_tampered = True
                tamper_alerts.append(f"Due Date Tampered! Blockchain recorded '{latest_chain_due_date}', but Database shows '{sql_date_raw}'!")
                
        return render_template(
            'blockchain_audit.html', 
            chain=activity_chain.chain, 
            is_valid=is_valid,
            db_tampered=db_tampered,
            tamper_alerts=tamper_alerts,
            activity=activity,
            activity_id=activity_id,
            user=current_user
        )

    except Exception as e:
        import traceback
        traceback.print_exc()
        flash('Error loading blockchain audit trail.', 'danger') 
        return redirect(request.referrer or '/')
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()

# ====================== LECTURER GENERAL BLOCKCHAIN INDEX (Handles Not Found) ======================
@app.route('/lecturer/blockchain_audit', methods=['GET'])
@lecturer_required
def lecturer_blockchain_audit():
    """
    Handles the generic /lecturer/blockchain_audit URL which causes the 'Not Found' error.
    It simply redirects the user to choose a specific activity.
    """
    flash('Please select a specific activity from the activity list to view its audit trail.', 'info')
    return redirect(url_for('lecturer_dashboard_redirect'))

# ====================== Plagiarism route (FIXED) ======================
# 1. The Background Worker Function
def background_plagiarism_worker(task_id, activity_id, submissions):
    try:
        final_reports = []
        total_subs = len(submissions)
        
        def analyze_single(primary_sub):
            highest_score = 0.0
            matches = []
            for comp_sub in submissions:
                if primary_sub['submission_id'] == comp_sub['submission_id']:
                    continue
                t1 = primary_sub['extracted_text'] or ""
                t2 = comp_sub['extracted_text'] or ""
                
                score, match_data = calculate_unified_similarity(t1, t2)
                
                if score > highest_score:
                    highest_score = score
                if score >= 0.1:
                    matches.append({
                        'source_name': comp_sub['fullname'],
                        'score': score,
                        'sub_id': comp_sub['submission_id']
                    })
            return {
                'student_name': primary_sub['fullname'],
                'primary_sub_id': primary_sub['submission_id'],
                'overall_score': highest_score,
                'matches': matches
            }

        completed_count = 0
        
        import concurrent.futures
        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
            futures = [executor.submit(analyze_single, sub) for sub in submissions]
            for future in concurrent.futures.as_completed(futures):
                final_reports.append(future.result())
                completed_count += 1
                
                PLAGIARISM_TASKS[task_id]['progress'] = int((completed_count / total_subs) * 100)

        final_reports.sort(key=lambda x: x['student_name'])
        
# ==========================================
        # DB SAVE FIX: Converting Numpy to Standard Float
        # ==========================================
        try:
            db_conn = get_db()
            cursor = db_conn.cursor()
            for report in final_reports:
                
                safe_score = float(report['overall_score']) 
                
                cursor.execute("""
                    UPDATE submissions 
                    SET plagiarism_score = %s 
                    WHERE submission_id = %s
                """, (safe_score, report['primary_sub_id']))
                
            db_conn.commit()
            cursor.close()
            db_conn.close()
            print("✅ Scores successfully saved to database!")
            
            # ---> NEW BLOCKCHAIN IMPROVEMENT (SPECIFIC LOGS) <---
            try:
                from local_blockchain import Blockchain
                activity_chain = Blockchain(identifier=activity_id)
                
                # Loop through and lock EVERY individual score!
                for report in final_reports:
                    safe_score = float(report['overall_score'])
                    activity_chain.new_log(
                        sender="SYSTEM_AUTO_CHECKER",
                        recipient=activity_id,
                        event_type="SCORE_LOCKED",
                        # Strict format so we can parse it easily later:
                        details=f"Sub_ID:{report['primary_sub_id']} | Score:{safe_score}"
                    )
                
                activity_chain.new_block(activity_chain.proof_of_work(activity_chain.last_block['proof']))
                print("⛓️ Blockchain: Specific Plagiarism Scores Locked.")
            except Exception as chain_error:
                print(f"Blockchain Error: {chain_error}")
            # ------------------------------------

        except Exception as db_e:
            print(f"❌ Database save error: {db_e}")

        # Mark as 100% complete and store the data temporarily
        PLAGIARISM_TASKS[task_id]['status'] = 'completed'
        PLAGIARISM_TASKS[task_id]['results'] = final_reports

    except Exception as e:
        PLAGIARISM_TASKS[task_id]['status'] = 'error'
        PLAGIARISM_TASKS[task_id]['error'] = str(e)

# ===================INSTANT MATRIX REPORT VIEWER===================
@app.route('/lecturer/matrix_report/<int:activity_id>')
@lecturer_required
def view_matrix_report(activity_id):
    db_conn = None
    cursor = None
    try:
        db_conn = get_db()
        cursor = db_conn.cursor(dictionary=True)
        
        # Fetch the lecturer's full name 
        cursor.execute("SELECT fullname FROM users WHERE username = %s", (session.get('username'),))
        current_user = cursor.fetchone()

        # ---> THE NEW FIX: Fetch the Activity Title <---
        cursor.execute("SELECT title FROM activities WHERE id = %s", (activity_id,))
        activity_record = cursor.fetchone()
        activity_title = activity_record['title'] if activity_record else f"Activity #{activity_id}"

        # Only fetch the MAXIMUM (latest) submission_id for each student
        cursor.execute("""
            SELECT s.submission_id, s.extracted_text, s.student_username, s.plagiarism_score, u.fullname 
            FROM submissions s 
            JOIN users u ON s.student_username = u.username 
            WHERE s.submission_id IN (
                SELECT MAX(submission_id) 
                FROM submissions 
                WHERE activity_id = %s 
                GROUP BY student_username
            )
        """, (activity_id,))
        submissions = cursor.fetchall()

        if len(submissions) < 2:
            flash('Not enough submissions to generate a report.', 'warning')
            return redirect(f'/lecturer/view_submissions/{activity_id}')

        final_reports = []
        for primary_sub in submissions:
            matches = []
            for comp_sub in submissions:
                if primary_sub['submission_id'] == comp_sub['submission_id']:
                    continue
                t1 = primary_sub['extracted_text'] or ""
                t2 = comp_sub['extracted_text'] or ""
                score, _ = calculate_unified_similarity(t1, t2)
                
                if score >= 0.1:
                    matches.append({
                        'source_name': comp_sub['fullname'],
                        'score': score,
                        'sub_id': comp_sub['submission_id']
                    })
                    
            final_reports.append({
                'student_name': primary_sub['fullname'],
                'primary_sub_id': primary_sub['submission_id'],
                'overall_score': primary_sub['plagiarism_score'] if primary_sub['plagiarism_score'] else 0.0, 
                'matches': matches
            })

        final_reports.sort(key=lambda x: x['student_name'])
        
        # ---> PASS THE NEW TITLE VARIABLE TO HTML <---
        return render_template('plagiarism_report.html', 
                               results=final_reports, 
                               activity_id=activity_id,
                               activity_title=activity_title, 
                               user=current_user)

    except Exception as e:
        import traceback
        traceback.print_exc()
        return f"System Error: {e}", 500
    finally:
        if cursor: cursor.close()
        if db_conn: db_conn.close()


# ====================== PLAGIARISM CHECKER ======================
# 2. The Route to Start the Check
@app.route('/lecturer/api/start_plagiarism_check/<int:activity_id>', methods=['POST'])
@lecturer_required
def start_plagiarism_check(activity_id):
    db_conn = get_db() 
    cursor = db_conn.cursor(dictionary=True)
    
    # THE FIX: Only fetch the MAXIMUM (latest) submission_id for each student!
    cursor.execute("""
        SELECT s.submission_id, s.extracted_text, s.student_username, u.fullname 
        FROM submissions s 
        JOIN users u ON s.student_username = u.username 
        WHERE s.submission_id IN (
            SELECT MAX(submission_id) 
            FROM submissions 
            WHERE activity_id = %s 
            GROUP BY student_username
        )
    """, (activity_id,))
    submissions = cursor.fetchall()
    cursor.close()
    db_conn.close()

    if len(submissions) < 2:
        return jsonify({'success': False, 'error': 'At least two submissions are required.'})

    import uuid
    task_id = str(uuid.uuid4())
    PLAGIARISM_TASKS[task_id] = {'status': 'processing', 'progress': 0}

    import threading
    thread = threading.Thread(target=background_plagiarism_worker, args=(task_id, activity_id, submissions))
    thread.start()

    return jsonify({'success': True, 'task_id': task_id})


# 3. The Route for the Browser to "Ping" for Progress
@app.route('/lecturer/api/check_progress/<task_id>')
@lecturer_required
def check_progress(task_id):
    if task_id not in PLAGIARISM_TASKS:
        return jsonify({'status': 'error', 'error': 'Task not found'})
    return jsonify(PLAGIARISM_TASKS[task_id])


# 4. The Final Route to Show the Page
@app.route('/lecturer/plagiarism_report/<int:activity_id>/<task_id>')
@lecturer_required
def view_plagiarism_report(activity_id, task_id):
    if task_id not in PLAGIARISM_TASKS or PLAGIARISM_TASKS[task_id]['status'] != 'completed':
        flash("Report expired or not finished.", "danger")
        return redirect(f'/lecturer/view_submissions/{activity_id}')
        
    results = PLAGIARISM_TASKS[task_id]['results']
    
    # Clean up memory
    del PLAGIARISM_TASKS[task_id] 
    
    return render_template('plagiarism_report.html', results=results, activity_id=activity_id)

# ====================== LOGOUT ======================
@app.route('/logout')
def logout():
    session.clear()
    return redirect('/login')

# 🚨 THE FIX: Make sure these bottom lines are touching the far left wall!
if __name__ == "__main__":
    print(app.url_map)
    app.run(debug=True)
