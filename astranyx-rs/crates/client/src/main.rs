//! Native entry point for Astranyx.

fn main() -> anyhow::Result<()> {
    astranyx_client::run()
}
