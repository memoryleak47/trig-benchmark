filename=$1
cp $1 src/scheduler.rs

echo TRIG RUN:
cargo r --release --bin trig -- --eq

echo INTEG RUN:
cargo r --release --bin integ -- --eq
