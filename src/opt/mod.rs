pub mod basic;
pub use basic::*;

use std::{collections::HashMap, fmt::Debug, time::{Duration, Instant}};
use crate::PartitionedCircuit;

pub struct PassMetrics {
    pub name: Option<&'static str>,
    pub props: HashMap<&'static str, Box<dyn Debug>>,
    pub children: Vec<PassMetrics>,
    pub elapsed: Duration,
    pub started: Instant,
    pub progress: bool
}

impl Debug for PassMetrics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.print(f, 0)
    }
}

impl PassMetrics {
    pub fn new() -> PassMetrics {
        PassMetrics {
            name: None,
            props: HashMap::new(),
            children: Vec::new(),
            elapsed: Duration::ZERO,
            started: Instant::now(),
            progress: false
        }
    }

    pub fn child(&mut self, metrics: PassMetrics) {
        self.children.push(metrics);
    }

    pub fn end(&mut self) {
        self.elapsed = self.started.elapsed();
    }

    pub fn name(&mut self, name: &'static str) {
        self.name = Some(name);
    }

    pub fn prop(&mut self, prop: &'static str, value: impl Debug + 'static) {
        self.props.insert(prop, Box::new(value));
    }

    pub fn progress(&mut self, prog: bool) {
        self.progress = prog;
    }

    fn print(&self, f: &mut std::fmt::Formatter<'_>, indent: usize) -> std::fmt::Result {
        writeln!(f, "{: <1$}{3} [{2:.2?}] {4}", 
            "", indent, self.elapsed, 
            if let Some(name) = self.name { name } else { "<unnamed>" },
            if self.progress { "" } else { "*" }
        )?;
        for (k, v) in &self.props {
            writeln!(f, "{: <1$}- {2} = {3:?}", "", indent, k, v)?;
        }
        for child in &self.children {
            child.print(f, indent + 2)?;
        }
        Ok(())
    }
}

pub trait OptimizationPass {
    fn run(&self, circ: PartitionedCircuit) -> (PartitionedCircuit, PassMetrics) {
        let mut metrics = PassMetrics::new();
        let (ocirc, prog) = self.run_with_metrics(circ, &mut metrics);
        metrics.progress(prog);
        metrics.end();
        (ocirc, metrics)
    }

    fn run_with_metrics(&self, circ: PartitionedCircuit, metrics: &mut PassMetrics) -> (PartitionedCircuit, bool);
}

macro_rules! impl_pass_tuple {
    ($($n:ident),+) => {
        impl<$($n: OptimizationPass),+> OptimizationPass for ($($n,)+) {
            fn run_with_metrics(&self, circ: PartitionedCircuit, metrics: &mut PassMetrics) -> (PartitionedCircuit, bool) {
                metrics.name("Sequential");
                #[allow(non_snake_case)]
                let ($($n,)+) = self;
                let mut prog = false;
                $(  
                    let (circ, pmetrics) = $n.run(circ);
                    prog |= pmetrics.progress;
                    metrics.child(pmetrics);
                )+
                (circ, prog)
            }
        }
    };
}

impl_pass_tuple!(U);
impl_pass_tuple!(U, V);
impl_pass_tuple!(U, V, W);
impl_pass_tuple!(U, V, W, X);
impl_pass_tuple!(U, V, W, X, Y);
impl_pass_tuple!(U, V, W, X, Y, Z);

pub struct RepeatUntilDone<T>(pub T);

impl<T: OptimizationPass> OptimizationPass for RepeatUntilDone<T> {
    fn run_with_metrics(&self, mut circ: PartitionedCircuit, metrics: &mut PassMetrics) -> (PartitionedCircuit, bool) {
        metrics.name("RepeatUntilDone");
        let mut pmetrics;
        let mut ever = false;
        loop {
            (circ, pmetrics) = self.0.run(circ);
            let prog = pmetrics.progress;
            metrics.child(pmetrics);
            if prog { 
                ever = true;
            } else {
                return (circ, ever)
            }
        }
    }
}
