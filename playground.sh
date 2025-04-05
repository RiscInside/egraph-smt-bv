#!/bin/bash

set -eu

cargo run --release playground.smt2 -j playground.out.json || true

while inotifywait -e modify playground.smt2; do
  sleep 0.5
  touch playground.html
  cargo run --release playground.smt2 -j playground.out.json || true
done
