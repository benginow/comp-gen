#!/usr/bin/env bash

RUST_BACKTRACE=1 RUST_LOG=debug,egg=info,z3=off $compgen_bin synth ruleset.json --config synth.json --synth 1.json
