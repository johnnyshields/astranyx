defmodule Astranyx.TurnCredentials do
  @moduledoc """
  Generates time-limited TURN credentials using HMAC-SHA1.

  This implements the TURN REST API (RFC 8489) for ephemeral credentials.
  The same shared secret must be configured in Coturn.

  ## Coturn config
  ```
  use-auth-secret
  static-auth-secret=your-shared-secret-here
  ```
  """

  # 1 hour
  @default_ttl 3600

  @doc """
  Generate ephemeral TURN credentials for a user.

  Returns a map with:
  - `username`: timestamp:user_id (Coturn expects this format)
  - `credential`: HMAC-SHA1 signature
  - `ttl`: time-to-live in seconds
  - `urls`: list of TURN server URLs
  """
  def generate(user_id, opts \\ []) do
    secret = get_secret()
    ttl = Keyword.get(opts, :ttl, @default_ttl)
    turn_urls = get_turn_urls()

    # Username format: expiry_timestamp:user_id
    expiry = System.system_time(:second) + ttl
    username = "#{expiry}:#{user_id}"

    # HMAC-SHA1 of username with shared secret
    credential =
      :crypto.mac(:hmac, :sha, secret, username)
      |> Base.encode64()

    %{
      username: username,
      credential: credential,
      ttl: ttl,
      urls: turn_urls
    }
  end

  defp get_secret do
    System.get_env("TURN_SECRET") ||
      Application.get_env(:astranyx, :turn_secret) ||
      raise "TURN_SECRET environment variable not set"
  end

  defp get_turn_urls do
    default_urls = ["turn:localhost:3478"]

    case System.get_env("TURN_URLS") do
      nil -> default_urls
      urls -> String.split(urls, ",", trim: true)
    end
  end
end
