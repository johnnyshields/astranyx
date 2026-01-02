defmodule AstranyxWeb.Router do
  use AstranyxWeb, :router

  pipeline :browser do
    plug :accepts, ["html"]
  end

  pipeline :api do
    plug :accepts, ["json"]
  end

  scope "/", AstranyxWeb do
    pipe_through :browser

    get "/", HelloController, :home
  end

  scope "/api", AstranyxWeb do
    pipe_through :api
  end
end
