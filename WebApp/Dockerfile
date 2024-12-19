# Compile C code first so we don't need to keep the C compiler in the final image
FROM gcc as builder

WORKDIR /app

# Copy the C code and compile it
COPY CalcGenus/CalcGenus.c CalcGenus.c
RUN gcc -O3 -ftree-vectorize -funroll-loops -Wall -std=c17 -pedantic -g -o CalcGenus CalcGenus.c

# Now we take a minimal python image and copy the compiled C binary to it
FROM python:3.9-slim

WORKDIR /app

COPY --from=builder /app/CalcGenus . 

# Python dependencies
COPY WebApp/requirements.txt requirements.txt
RUN pip install --no-cache-dir -r requirements.txt

# Copy the rest of the files
COPY CalcGenus/adjacency_lists/* adjacency_lists/
COPY WebApp/main.py main.py
COPY WebApp/static/* static/

EXPOSE 8080

CMD gunicorn --workers=$((2 * $(python -c 'import os; print(os.cpu_count())') + 1)) --threads=1 --bind=0.0.0.0:8080 --timeout 600 main:app

