#!/bin/bash

docker build --tag 'genus' -f ./Dockerfile ..

open http://localhost:8080 || start chrome \"http://localhost:8080\" || google-chrome 'http://localhost:8080' || echo 'Could not open browser automatically. Please open http://localhost:8080 manually'
docker run -t -i -p 8080:8080 'genus'
