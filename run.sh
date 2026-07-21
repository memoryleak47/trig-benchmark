filename=$1
cp $1 src/scheduler.rs

[[ $(pwd) == *"trig" ]] && cargo r --release --bin trig -- --eq
[[ $(pwd) == *"integ" ]] && cargo r --release --bin integ -- --eq
