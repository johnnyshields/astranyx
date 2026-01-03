defmodule Astranyx.TurnCredentialsTest do
  use ExUnit.Case, async: true

  alias Astranyx.TurnCredentials

  setup do
    # Set test environment variables
    System.put_env("TURN_SECRET", "test-secret-123")
    System.put_env("TURN_URLS", "turn:test.example.com:3478,turns:test.example.com:5349")

    on_exit(fn ->
      System.delete_env("TURN_SECRET")
      System.delete_env("TURN_URLS")
    end)

    :ok
  end

  describe "generate/2" do
    test "returns credentials with correct structure" do
      credentials = TurnCredentials.generate("user123")

      assert is_map(credentials)
      assert Map.has_key?(credentials, :username)
      assert Map.has_key?(credentials, :credential)
      assert Map.has_key?(credentials, :ttl)
      assert Map.has_key?(credentials, :urls)
    end

    test "username contains expiry timestamp and user_id" do
      credentials = TurnCredentials.generate("user123")

      [expiry_str, user_id] = String.split(credentials.username, ":")
      assert user_id == "user123"

      expiry = String.to_integer(expiry_str)
      now = System.system_time(:second)
      # Default TTL is 3600 seconds
      assert expiry > now
      assert expiry <= now + 3600
    end

    test "credential is base64 encoded HMAC-SHA1" do
      credentials = TurnCredentials.generate("user123")

      # Verify credential is valid base64
      assert {:ok, _decoded} = Base.decode64(credentials.credential)

      # Verify HMAC-SHA1 produces correct result
      expected_credential =
        :crypto.mac(:hmac, :sha, "test-secret-123", credentials.username)
        |> Base.encode64()

      assert credentials.credential == expected_credential
    end

    test "default TTL is 3600 seconds" do
      credentials = TurnCredentials.generate("user123")
      assert credentials.ttl == 3600
    end

    test "custom TTL is respected" do
      credentials = TurnCredentials.generate("user123", ttl: 7200)
      assert credentials.ttl == 7200

      [expiry_str, _user_id] = String.split(credentials.username, ":")
      expiry = String.to_integer(expiry_str)
      now = System.system_time(:second)
      # Should be within 7200 seconds
      assert expiry <= now + 7200
    end

    test "returns configured TURN URLs" do
      credentials = TurnCredentials.generate("user123")

      assert credentials.urls == [
               "turn:test.example.com:3478",
               "turns:test.example.com:5349"
             ]
    end

    test "generates different credentials for different users" do
      creds1 = TurnCredentials.generate("user1")
      creds2 = TurnCredentials.generate("user2")

      assert creds1.username != creds2.username
      assert creds1.credential != creds2.credential
    end

    test "generates credentials that change over time" do
      creds1 = TurnCredentials.generate("user123")
      Process.sleep(1100)
      creds2 = TurnCredentials.generate("user123")

      # Username will differ because expiry timestamp changes
      assert creds1.username != creds2.username
    end
  end

  describe "generate/2 with default TURN URLs" do
    setup do
      System.delete_env("TURN_URLS")
      :ok
    end

    test "uses localhost default when TURN_URLS not set" do
      credentials = TurnCredentials.generate("user123")
      assert credentials.urls == ["turn:localhost:3478"]
    end
  end

  describe "generate/2 without secret" do
    setup do
      System.delete_env("TURN_SECRET")
      :ok
    end

    test "raises error when TURN_SECRET not set" do
      assert_raise RuntimeError, ~r/TURN_SECRET/, fn ->
        TurnCredentials.generate("user123")
      end
    end
  end

  describe "generate/2 with application config" do
    setup do
      System.delete_env("TURN_SECRET")
      Application.put_env(:astranyx, :turn_secret, "app-config-secret")

      on_exit(fn ->
        Application.delete_env(:astranyx, :turn_secret)
      end)

      :ok
    end

    test "falls back to application config when env var not set" do
      credentials = TurnCredentials.generate("user123")

      expected_credential =
        :crypto.mac(:hmac, :sha, "app-config-secret", credentials.username)
        |> Base.encode64()

      assert credentials.credential == expected_credential
    end
  end
end
