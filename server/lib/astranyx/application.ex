defmodule Astranyx.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    children = [
      AstranyxWeb.Telemetry,
      {DNSCluster, query: Application.get_env(:astranyx, :dns_cluster_query) || :ignore},
      {Phoenix.PubSub, name: Astranyx.PubSub},

      # Lobby for room management (no game simulation - that's P2P)
      Astranyx.Game.Lobby,

      # Phoenix endpoint (last)
      AstranyxWeb.Endpoint
    ]

    opts = [strategy: :one_for_one, name: Astranyx.Supervisor]
    Supervisor.start_link(children, opts)
  end

  @impl true
  def config_change(changed, _new, removed) do
    AstranyxWeb.Endpoint.config_change(changed, removed)
    :ok
  end
end
