defmodule AstranyxWeb.Router do
  use AstranyxWeb, :router

  pipeline :api do
    plug :accepts, ["json"]
  end

  scope "/api", AstranyxWeb do
    pipe_through :api
  end
end
