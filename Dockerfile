FROM python:3.12-slim
ENV PYTHONUNBUFFERED=1 PIP_NO_CACHE_DIR=1
WORKDIR /app
COPY requirements.txt .
RUN pip install -r requirements.txt
COPY . .
ENV XEROXUID_DATA_DIR=/data \
    XEROXUID_DB=/data/xeroxuid.db \
    XEROXUID_SECURE_COOKIES=1
EXPOSE 8080
# One worker: the app keeps fetch locks in memory and uses SQLite.
CMD ["gunicorn", "-w", "1", "--threads", "8", "-b", "0.0.0.0:8080", "--timeout", "120", "app:app"]
