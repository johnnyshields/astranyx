# Ensure the endpoint and application are started before tests run
{:ok, _} = Application.ensure_all_started(:astranyx)

ExUnit.start()
