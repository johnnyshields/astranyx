defmodule AstranyxWeb.HelloController do
  use AstranyxWeb, :controller

  def home(conn, _params) do
    conn
    |> put_resp_content_type("text/html")
    |> send_resp(200, """
    <!DOCTYPE html>
    <html>
    <head>
      <title>Astranyx Server</title>
      <style>
        body {
          font-family: system-ui, sans-serif;
          display: flex;
          justify-content: center;
          align-items: center;
          min-height: 100vh;
          margin: 0;
          background: #1a1a2e;
          color: #eee;
        }
        h1 { font-size: 3rem; }
      </style>
    </head>
    <body>
      <h1>Astranyx Server</h1>
    </body>
    </html>
    """)
  end
end
